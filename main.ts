// tiny-stack-vm: a small interpreter for make.fun's tiny stack ISA (v1).
// One pass per program: fetch, bounds-check, stack-check, then execute.
// Every machine fault is thrown as its trap code and caught per program,
// so the bytes written before the fault survive with the trap's exit code.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

type Res = { buf: Uint8Array; code: number };

// Opcode validity, indexed by opcode byte; built once at load instead of
// re-evaluating a multi-range boolean on every executed instruction.
const KNOWN = new Uint8Array(256);
for (const r of [[0, 7], [16, 34], [48, 52], [64, 65], [80, 83]])
  for (let i = r[0]; i <= r[1]; i++) KNOWN[i] = 1;

// Stack effect per opcode, built once; replaces the per-step if/else chain
// (and its per-step array literals) in the hot loop.
const POPS = new Uint8Array(256);
const PUSHES = new Uint8Array(256);
for (let i = 0; i < 8; i++) { POPS[i] = [0, 0, 0, 1, 1, 2, 2, 3][i]; PUSHES[i] = [0, 1, 1, 0, 2, 2, 3, 3][i]; }
for (let i = 16; i <= 34; i++) { POPS[i] = i === 23 || i === 27 ? 1 : 2; PUSHES[i] = 1; }
POPS[49] = 1; POPS[50] = 1; POPS[64] = 1; PUSHES[64] = 1;
POPS[65] = 2;
POPS[80] = 1; POPS[81] = 1; POPS[83] = 1;
PUSHES[82] = 1;

function run(P: Uint8Array, N: Uint8Array): Res {
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // return addresses
  const M = new Int32Array(256); // word memory
  const buf = new Uint8Array(65536);
  let sp = 0, cp = 0, len = 0, pos = 0, pc = 0, steps = 0;
  const die = (t: number): never => { throw t; };
  try {
    for (;;) {
      if (steps === 1000000) die(10);
      if (pc < 0 || pc >= P.length) die(9);
      const op = P[pc];
      if (!KNOWN[op]) die(5);
      const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
      if (pc + imm >= P.length) die(9);
      steps++;
      // pops / pushes of this opcode, checked before it may trap on its own
      const pops = POPS[op], pushes = PUSHES[op];
      if (sp < pops) die(2);
      if (sp - pops + pushes > 256) die(3);
      const nx = pc + 1 + imm;
      pc = nx;
      if (op >= 16 && op <= 34 && op !== 23 && op !== 27) {
        const b = S[--sp], a = S[--sp];
        let r = 0;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (!b) die(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (!b) die(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (!b) die(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (!b) die(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        S[sp++] = r;
        continue;
      }
      switch (op) {
        case 0: return { buf: buf.slice(0, len), code: 0 };
        case 1: S[sp++] = (P[nx - 1] << 24) >> 24; break;
        case 2: S[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break;
        case 3: sp--; break;
        case 4: S[sp] = S[sp - 1]; sp++; break;
        case 5: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
        case 6: S[sp] = S[sp - 2]; sp++; break;
        case 7: { const t = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = t; break; }
        case 23: S[sp - 1] = -S[sp - 1] | 0; break;
        case 27: S[sp - 1] = ~S[sp - 1]; break;
        case 48: case 49: case 50: {
          const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
          if (op === 48 || (S[--sp] === 0) === (op === 49)) pc = nx + rel;
          break;
        }
        case 51:
          if (cp === 64) die(7);
          C[cp++] = nx; pc = P[nx - 2] | (P[nx - 1] << 8); break;
        case 52:
          if (cp === 0) die(8);
          pc = C[--cp]; break;
        case 64: {
          const a = S[sp - 1];
          if (a < 0 || a > 255) die(6);
          S[sp - 1] = M[a]; break;
        }
        case 65: {
          const a = S[sp - 1];
          if (a < 0 || a > 255) die(6);
          M[a] = S[sp - 2]; sp -= 2; break;
        }
        case 80: {
          const s = String(S[sp - 1]);
          if (len + s.length > 65536) die(11);
          sp--;
          for (let i = 0; i < s.length; i++) buf[len++] = s.charCodeAt(i);
          break;
        }
        case 81:
          if (len === 65536) die(11);
          buf[len++] = S[--sp] & 255; break;
        case 82: S[sp++] = pos < N.length ? N[pos++] : -1; break;
        case 83: return { buf: buf.slice(0, len), code: S[--sp] & 255 };
      }
    }
  } catch (t) {
    return { buf: buf.slice(0, len), code: t as number };
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.buf);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
