// Tiny stack VM for make.fun's ISA (kit ISA.md). Reads /input/<id>/program.bin
// + input.bin, writes /output/<id>/stdout.bin + exit.txt for every instance.
// Deterministic: no clock, network, or environment variation.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, pops, pushes]; unknown bytes keep imm 255.
const IMM = new Uint8Array(256).fill(255), POPN = new Uint8Array(256), PUSHN = new Uint8Array(256);
for (const [op, im, po, pu] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1],
  [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1], [33, 0, 2, 1],
  [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0],
  [82, 0, 0, 1], [83, 0, 1, 0],
]) { IMM[op] = im; POPN[op] = po; PUSHN[op] = pu; }

const MIN = -2147483648;

function execute(prog, input) {
  const n = prog.length;
  const d = new Int32Array(256);
  let sp = 0;
  const c = new Int32Array(64);
  let cp = 0;
  const m = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  const dg = new Uint8Array(12);
  let ip = 0, pc = 0, steps = 0;
  const done = (code) => ({ out: out.slice(0, ol), code });
  for (;;) {
    if (steps === 1000000) return done(10); // step limit, checked first
    if (pc < 0 || pc >= n) return done(9); // pc outside the program
    const op = prog[pc], im = IMM[op];
    if (im === 255) return done(5); // unknown opcode
    if (pc + im >= n) return done(9); // immediate cut off by program end
    steps++;
    const next = pc + 1 + im;
    if (sp < POPN[op]) return done(2); // underflow, checked before own traps
    if (sp - POPN[op] + PUSHN[op] > 256) return done(3); // overflow
    pc = next;
    switch (op) {
      case 0: return done(0); // HALT
      case 1: d[sp++] = (prog[pc - 1] << 24) >> 24; break; // PUSH8 sign-extended
      case 2: // PUSH32 little-endian
        d[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24);
        break;
      case 3: sp--; break; // POP
      case 4: d[sp] = d[sp - 1]; sp++; break; // DUP
      case 5: { const t = d[sp - 1]; d[sp - 1] = d[sp - 2]; d[sp - 2] = t; break; } // SWAP
      case 6: d[sp] = d[sp - 2]; sp++; break; // OVER
      case 7: { // ROT (a b c -- b c a)
        const a = d[sp - 3]; d[sp - 3] = d[sp - 2]; d[sp - 2] = d[sp - 1]; d[sp - 1] = a;
        break;
      }
      case 23: d[sp - 1] = -d[sp - 1] | 0; break; // NEG, -MIN wraps to MIN
      case 27: d[sp - 1] = ~d[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32:
      case 33: case 34: {
        const b = d[sp - 1], a = d[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b); // exact low 32 bits
        else if (op === 19) {
          if (b === 0) return done(4);
          r = a === MIN && b === -1 ? a : (a / b) | 0; // MIN/-1 stays MIN
        } else if (op === 20) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0; // x%-1 is 0, sign follows a
        } else if (op === 21) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // unsigned divide
        } else if (op === 22) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0; // unsigned remainder
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2; d[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) { const v = d[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc += rel; // target unchecked: out-of-range traps 9 next step
        break;
      }
      case 51: // CALL, unsigned 16-bit target, 64-deep
        if (cp === 64) return done(7);
        c[cp++] = pc;
        pc = prog[pc - 2] | (prog[pc - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return done(8);
        pc = c[--cp];
        break;
      case 64: { // LOAD
        const a = d[sp - 1];
        if (a < 0 || a > 255) return done(6);
        d[sp - 1] = m[a];
        break;
      }
      case 65: { // STORE (value address --), address on top
        const a = d[sp - 1];
        if (a < 0 || a > 255) return done(6);
        m[a] = d[sp - 2]; sp -= 2;
        break;
      }
      case 80: { // PRINT: decimal, '-' only, no padding/newline
        const v = d[sp - 1], neg = v < 0;
        let u = neg ? -v : v, k = 0; // -MIN is 2147483648, still exact
        if (u === 0) dg[k++] = 48;
        else while (u > 0) { dg[k++] = 48 + (u % 10); u = Math.floor(u / 10); }
        const len = k + (neg ? 1 : 0);
        if (ol + len > 65536) return done(11); // writes none of its bytes
        sp--;
        let j = ol;
        if (neg) out[j++] = 45;
        while (k > 0) out[j++] = dg[--k];
        ol = j;
        break;
      }
      case 81: // PUTC: low byte
        if (ol + 1 > 65536) return done(11);
        out[ol++] = d[--sp] & 255;
        break;
      case 82: // IN: -1 once input is used up, every time after
        d[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 83: return done(d[--sp] & 255); // EXIT: low byte
      default: return done(5);
    }
  }
}

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN).sort()) {
  const dir = join(OUT, id);
  mkdirSync(dir, { recursive: true });
  let r;
  try {
    r = execute(
      new Uint8Array(readFileSync(join(IN, id, 'program.bin'))),
      new Uint8Array(readFileSync(join(IN, id, 'input.bin'))),
    );
  } catch {
    // An unreadable instance still gets a well-formed answer, never a crash
    // that would take the other instances down with it.
    r = { out: new Uint8Array(0), code: 0 };
  }
  writeFileSync(join(dir, 'stdout.bin'), r.out);
  writeFileSync(join(dir, 'exit.txt'), `${r.code}\n`);
}
