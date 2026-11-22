import { mkdirSync, readFileSync, writeFileSync } from "node:fs";


function run(prog: Uint8Array, inp: Uint8Array): { out: Uint8Array; exit: number } {
  const n = prog.length;
  const st = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const digits = new Uint8Array(12);

  const fin = (exit: number) => ({ out: out.slice(0, ol), exit });

  for (;;) {
    if (steps === 1000000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = prog[pc];
    let imm = 0;
    let pop = 0;
    let push = 0;
    switch (op) {
      case 0x00: break;
      case 0x01: imm = 1; push = 1; break;
      case 0x02: imm = 4; push = 1; break;
      case 0x03: pop = 1; break;
      case 0x04: pop = 1; push = 2; break;
      case 0x05: pop = 2; push = 2; break;
      case 0x06: pop = 2; push = 3; break;
      case 0x07: pop = 3; push = 3; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22:
        pop = 2; push = 1; break;
      case 0x17: case 0x1b: pop = 1; push = 1; break;
      case 0x30: imm = 2; break;
      case 0x31: case 0x32: imm = 2; pop = 1; break;
      case 0x33: imm = 2; break;
      case 0x34: break;
      case 0x40: pop = 1; push = 1; break;
      case 0x41: pop = 2; break;
      case 0x50: case 0x51: case 0x53: pop = 1; break;
      case 0x52: push = 1; break;
      default: return fin(5);
    }
    if (pc + imm >= n) return fin(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < pop) return fin(2);
    if (sp - pop + push > 256) return fin(3);
    pc = nx;

    switch (op) {
      case 0x00: return fin(0);
      case 0x01: st[sp++] = (prog[nx - 1] << 24) >> 24; break;
      case 0x02:
        st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: { const t = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = t; break; }
      case 0x17: st[sp - 1] = -st[sp - 1] | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return fin(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return fin(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return fin(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return fin(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = st[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return fin(7);
        cs[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return fin(8);
        pc = cs[--cp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1];
        const v = st[sp - 2];
        if (addr < 0 || addr >= 256) return fin(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        let u = st[--sp];
        let neg = false;
        if (u < 0) { neg = true; u = -u; }
        let t = 0;
        if (u === 0) digits[t++] = 48;
        else while (u > 0) { digits[t++] = 48 + (u % 10); u = Math.floor(u / 10); }
        const len = t + (neg ? 1 : 0);
        if (ol + len > 65536) return fin(11);
        if (neg) out[ol++] = 45;
        while (t > 0) out[ol++] = digits[--t];
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return fin(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52:
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: return fin(st[--sp] & 255);
    }
  }
}

for (let i = 1; i <= 40; i++) {
  const id = "i" + String(i).padStart(3, "0");
  try {
    const prog = readFileSync(`/input/${id}/program.bin`);
    const inp = readFileSync(`/input/${id}/input.bin`);
    const r = run(prog, inp);
    mkdirSync(`/output/${id}`, { recursive: true });
    writeFileSync(`/output/${id}/stdout.bin`, r.out);
    writeFileSync(`/output/${id}/exit.txt`, String(r.exit));
  } catch {
    try {
      mkdirSync(`/output/${id}`, { recursive: true });
      writeFileSync(`/output/${id}/stdout.bin`, new Uint8Array(0));
      writeFileSync(`/output/${id}/exit.txt`, "0");
    } catch { /* nothing more we can do */ }
  }
}
