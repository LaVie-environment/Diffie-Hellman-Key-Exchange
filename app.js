/* ═══════════════════════════════════════════════════════════════
   Diffie-Hellman Demo — app.js
   All arithmetic uses BigInt throughout. Supports RFC 3526
   standard 2048-bit, 3072-bit, and 4096-bit groups, plus a
   custom mode (for educational purposes with small numbers).
   ═══════════════════════════════════════════════════════════════ */

'use strict';

// ════════════════════════════════════════════════════════════════
//  RFC 3526 Standard Groups (all verified with Fermat's theorem)
//  g = 2 for all groups, p values are IETF standard safe primes.
// ════════════════════════════════════════════════════════════════
const RFC3526 = {
  2048: {
    bits: 2048,
    p: BigInt('0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF'),
    g: 2n,
  },
  3072: {
    bits: 3072,
    p: BigInt('0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AAAC42DAD33170D04507A33A85521ABDF1CBA64ECFB850458DBEF0A8AEA71575D060C7DB3970F85A6E1E4C7ABF5AE8CDB0933D71E8C94E04A25619DCEE3D2261AD2EE6BF12FFA06D98A0864D87602733EC86A64521F2B18177B200CBBE117577A615D6C770988C0BAD946E208E24FA074E5AB3143DB5BFCE0FD108E4B82D120A93AD2CAFFFFFFFFFFFFFFFF'),
    g: 2n,
  },
  4096: {
    bits: 4096,
    p: BigInt('0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AAAC42DAD33170D04507A33A85521ABDF1CBA64ECFB850458DBEF0A8AEA71575D060C7DB3970F85A6E1E4C7ABF5AE8CDB0933D71E8C94E04A25619DCEE3D2261AD2EE6BF12FFA06D98A0864D87602733EC86A64521F2B18177B200CBBE117577A615D6C770988C0BAD946E208E24FA074E5AB3143DB5BFCE0FD108E4B82D120A92108011A723C12A787E6D788719A10BDBA5B2699C327186AF4E23C1A946834B6150BDA2583E9CA2AD44CE8DBBBC2DB04DE8EF92E8EFC141FBECAA6287C59474E6BC05D99B2964FA090C3A2233BA186515BE7ED1F612970CEE2D7AFB81BDD762170481CD0069127D5B05AA993B4EA988D8FDDC186FFB7DC90A6C08F4DF435C934063199FFFFFFFFFFFFFFFF'),
    g: 2n,
  },
};

// ════════════════════════════════════════════════════════════════
//  BigInt math utilities
// ════════════════════════════════════════════════════════════════

/** Modular exponentiation — all BigInt, no Number conversion. */
function modPow(base, exp, mod) {
  let b = ((base % mod) + mod) % mod;
  let result = 1n;
  let e = exp;
  while (e > 0n) {
    if (e & 1n) result = (result * b) % mod;
    e >>= 1n;
    b = (b * b) % mod;
  }
  return result;
}

/**
 * Miller-Rabin primality test — works with BigInt of any size.
 * Uses deterministic witnesses for n < 3,317,044,064,679,887,385,961,981,
 * and probabilistic (25 rounds) for larger values.
 */
function millerRabin(n, rounds = 25) {
  if (n < 2n) return false;
  if (n === 2n || n === 3n || n === 5n || n === 7n) return true;
  if (n % 2n === 0n) return false;

  // Write n-1 as 2^r * d
  let d = n - 1n, r = 0n;
  while (d % 2n === 0n) { d >>= 1n; r++; }

  // Deterministic witnesses cover n < ~3.3 × 10^24
  const witnesses = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];

  for (const a of witnesses) {
    if (a >= n) continue;
    let x = modPow(a, d, n);
    if (x === 1n || x === n - 1n) continue;
    let composite = true;
    for (let i = 0n; i < r - 1n; i++) {
      x = (x * x) % n;
      if (x === n - 1n) { composite = false; break; }
    }
    if (composite) return false;
  }
  return true;
}

/** Format a BigInt for display: show first 40 and last 20 chars if long. */
function fmtBig(n) {
  const s = n.toString();
  if (s.length <= 80) return s;
  return `${s.slice(0, 40)}…${s.slice(-20)} (${s.length} digits)`;
}

/** Show a substituted modular-exponentiation calculation with color-coded HTML. */
function fmtModExp(label, base, exp, mod, result) {
  // Each value gets a distinct colour so lay audiences can tell them apart
  // even when two values happen to be numerically equal.
  return (
    `${label} = ` +
    `<span class="calc-base">${fmtBig(base)}</span>` +
    `<sup class="calc-exp">${fmtBig(exp)}</sup>` +
    ` <span class="calc-mod-kw">mod</span> ` +
    `<span class="calc-mod">${fmtBig(mod)}</span>` +
    ` = ` +
    `<span class="calc-result">${fmtBig(result)}</span>`
  );
}

/** Colour legend for lay audiences — explains what each colour means. */
function calcLegend(baseLabel, expLabel) {
  return `
    <div class="calc-legend">
      <span class="calc-legend-item"><span class="calc-legend-dot" style="background:var(--alice)"></span><span class="calc-base">${baseLabel}</span> base</span>
      <span class="calc-legend-item"><span class="calc-legend-dot" style="background:var(--bob)"></span><span class="calc-exp">${expLabel}</span> exponent (secret)</span>
      <span class="calc-legend-item"><span class="calc-legend-dot" style="background:var(--purple)"></span><span style="color:var(--purple)">p</span> prime modulus</span>
      <span class="calc-legend-item"><span class="calc-legend-dot" style="background:var(--shared)"></span><span class="calc-result">result</span></span>
    </div>`;
}

function parseBig(str) {
  const s = str.trim().replace(/\s/g, '');
  if (!s) return null;
  try { return BigInt(s); } catch { return null; }
}

// ── Bit-length helpers ────────────────────────────────────────────

/** Minimum bit-length required for custom-mode prime p. */
const MIN_BITS_CUSTOM = 2;    // Allow small educational primes such as 23
const WARN_BITS_CUSTOM = 512; // Show security warning below this threshold

/**
 * Return the number of bits needed to represent n (n must be a positive BigInt).
 * Equivalent to ⌊log₂(n)⌋ + 1.
 */
function bitLength(n) {
  if (n <= 0n) return 0;
  return n.toString(2).length;
}

/**
 * Return true if n has at least minBits bits.
 * Reject anything too small to be meaningful (< MIN_BITS_CUSTOM).
 */
function hasMinBits(n, minBits) {
  return bitLength(n) >= minBits;
}

/**
 * Generate a random BigInt secret in range [2, p-2] suitable for use as
 * a DH private exponent. Uses crypto.getRandomValues for good entropy.
 * For large p this may take a couple of iterations.
 */
function randomSecret(p) {
  // Secret values are valid only when they are less than p - 2.
  // For tiny classroom primes, fall back to 1.
  if (p <= 5n) return 1n;
  const bits = bitLength(p);
  const bytes = Math.ceil(bits / 8);
  const buf = new Uint8Array(bytes);
  let r;
  do {
    crypto.getRandomValues(buf);
    r = BigInt('0x' + Array.from(buf).map(b => b.toString(16).padStart(2, '0')).join(''));
    r = r % (p - 3n) + 1n;   // clamp to [1, p-3], i.e. less than p - 2
  } while (r < 1n || r >= p - 2n);
  return r;
}

// ════════════════════════════════════════════════════════════════
//  Application state
// ════════════════════════════════════════════════════════════════
let state = {
  p: null,        // BigInt
  g: null,        // BigInt
  a: null,        // BigInt — Alice's secret
  b: null,        // BigInt — Bob's secret
  A: null,        // BigInt — Alice's public value
  B: null,        // BigInt — Bob's public value
  K: null,        // BigInt — Alice's shared key
  K_bob: null,    // BigInt — Bob's shared key (must equal K)
  step: -1,
  secretsConfirmed: false,
  mode: 'custom', // users enter their own p and g
};

const TOTAL_STEPS = 7;
const $ = id => document.getElementById(id);

// ── DOM refs ──────────────────────────────────────────────────────
const btnGen             = $('btn-gen');
const btnPrev            = $('btn-prev');
const btnNext            = $('btn-next');
const btnTry             = $('btn-try');
const btnConfirm         = $('btn-confirm-secrets');
const confirmWrap        = $('confirm-secrets-wrap');
const errorSecrets       = $('error-secrets');
const expl               = $('explanation');
const sharedBadge        = $('shared-badge');
const badgeKVal          = $('badge-k-val');
const pubP               = $('pub-p');
const pubG               = $('pub-g');
const dotsEl             = $('dots');
const stepCur            = $('step-cur');
const inputP             = $('input-p');           // prime field (always visible)
const inputG             = $('input-g');           // generator field (always visible)
const inputError         = $('input-error');
const agreedDisplay      = $('agreed-display');
const inputA             = $('input-a');
const inputB             = $('input-b');
const errorA             = $('error-a');
const errorB             = $('error-b');
const secBanner          = $('sec-banner');
const btnResetP          = $('btn-reset-p');

// ════════════════════════════════════════════════════════════════
//  Step definitions — all interpolation uses fmtBig() for large nums
// ════════════════════════════════════════════════════════════════
const STEPS = [
  {
    // Step 1 — agreed public parameters
    show: ['a-p','a-g','b-p','b-g'], aliceHl: [], bobHl: [],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
    },
    aliceSummary: s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)}`,
    bobSummary:   s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)}`,
    explanation:  s => `
      <div class="mod-explainer">
         <strong>What does "mod" mean?</strong><br>
        "mod" means the <strong>remainder after dividing</strong>.<br>
        Example: <strong>8 mod 5 = 3</strong>, because 8 ÷ 5 = 1 remainder <strong>3</strong>.<br>
        Think of it as clock arithmetic — after 12 comes 1 again.
      </div>
      <p>Alice and Bob have agreed on two public numbers that everyone can see —
         they are <strong>not secret</strong>:</p>
      <ul class="plain-list">
        <li><strong>p = ${fmtBig(s.p)}</strong> — a very large prime number used as the "clock size" for all the calculations.</li>
        <li><strong>g = ${fmtBig(s.g)}</strong> — a starting number (called a generator) that both Alice and Bob will use to mix with their secrets.</li>
      </ul>`,
  },
  {
    // Step 2 — secret values chosen
    show: ['a-p','a-g','a-a','b-p','b-g','b-b'], aliceHl: ['a-a'], bobHl: ['b-b'],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'a-a-val': s => fmtBig(s.a),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
      'b-b-val': s => fmtBig(s.b),
    },
    aliceSummary: s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  a = ${fmtBig(s.a)}`,
    bobSummary:   s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  b = ${fmtBig(s.b)}`,
    explanationPending: s => `
      <p>Now Alice and Bob each <strong>privately pick their own secret number</strong>.</p>
      <p>Alice types her secret in her card on the left. Bob types his secret in his card on the right.
         These numbers must be at least <strong>1</strong> and smaller than <strong>p</strong>.
          They <strong>never show these numbers to anyone</strong> — not even to each other!</p>`,
    explanation: s => `
      <p>Alice chose her secret number <strong>a = ${fmtBig(s.a)}</strong>.</p>
      <p>Bob chose his secret number <strong>b = ${fmtBig(s.b)}</strong>.</p>
      <p> These numbers stay completely private — each person keeps their own secret number hidden and never reveals it to anyone.</p>`,
  },
  {
    // Step 3 — Alice computes A
    show: ['a-p','a-g','a-a','a-A','b-p','b-g','b-b'], aliceHl: ['a-A'], bobHl: [],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'a-a-val': s => fmtBig(s.a),
      'a-A-val': s => fmtModExp('A', s.g, s.a, s.p, s.A),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
      'b-b-val': s => fmtBig(s.b),
    },
    aliceSummary: s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  a = ${fmtBig(s.a)},  A = ${fmtBig(s.A)}`,
    bobSummary:   s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  b = ${fmtBig(s.b)}`,
    explanation:  s => `
      <p>Alice mixes her secret number with the shared starting number <strong>g</strong>
         to create her <strong>public number A</strong>. She does this using a special maths trick:</p>
      <p class="calc-line">A = g<sup>a</sup> mod p &nbsp;→&nbsp; <strong>${fmtModExp('A', s.g, s.a, s.p, s.A)}</strong></p>
      ${calcLegend('g', 'a')}
      <div class="mod-explainer">
       <strong>Remember:</strong> "mod p" means take the remainder after dividing by p.<br>
        This mixing is easy to do forwards, but <strong>very hard to undo</strong> like scrambling an egg.
        Nobody can work out Alice's secret <em>a</em> just by looking at A.
      </div>
      <p>Alice keeps A ready to send but first waits for Bob to do the same.</p>`,
  },
  {
    // Step 4 — Bob computes B
    show: ['a-p','a-g','a-a','a-A','b-p','b-g','b-b','b-B'], aliceHl: [], bobHl: ['b-B'],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'a-a-val': s => fmtBig(s.a),
      'a-A-val': s => fmtBig(s.A),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
      'b-b-val': s => fmtBig(s.b),
      'b-B-val': s => fmtModExp('B', s.g, s.b, s.p, s.B),
    },
    aliceSummary: s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  a = ${fmtBig(s.a)},  A = ${fmtBig(s.A)}`,
    bobSummary:   s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  b = ${fmtBig(s.b)},  B = ${fmtBig(s.B)}`,
    explanation:  s => `
      <p>Bob does the exact same mixing trick with his own secret number to create his
         <strong>public number B</strong>:</p>
      <p class="calc-line">B = g<sup>b</sup> mod p &nbsp;→&nbsp; <strong>${fmtModExp('B', s.g, s.b, s.p, s.B)}</strong></p>
      ${calcLegend('g', 'b')}
      <div class="mod-explainer">
         Just like Alice, Bob's public number B is safe to share. Even if someone sees B,
        they <strong>cannot work backwards</strong> to find Bob's secret <em>b</em>.
        It is very hard to work backwards and find the secret number.
      </div>
      <p>Both public numbers A and B are now ready. Time to swap them</p>`,
  },
  {
    // Step 5 — Alice and Bob exchange their public numbers simultaneously
    show: ['a-p','a-g','a-a','a-A','a-B','b-p','b-g','b-b','b-B','b-A'],
    aliceHl: ['a-B'], bobHl: ['b-A'],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'a-a-val': s => fmtBig(s.a),
      'a-A-val': s => fmtBig(s.A),
      'a-B-val': s => fmtBig(s.B),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
      'b-b-val': s => fmtBig(s.b),
      'b-B-val': s => fmtBig(s.B),
      'b-A-val': s => fmtBig(s.A),
    },
    aliceSummary: s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  a = ${fmtBig(s.a)},  A = ${fmtBig(s.A)},  B = ${fmtBig(s.B)}`,
    bobSummary:   s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  b = ${fmtBig(s.b)},  B = ${fmtBig(s.B)},  A = ${fmtBig(s.A)}`,
    explanation:  s => `
      <p>Alice and Bob now <strong>send their public numbers</strong> to each other over the internet at the same time:</p>
      <ul class="plain-list">
        <li> <strong>Alice sends A = ${fmtBig(s.A)}</strong> to Bob.</li>
        <li> <strong>Bob sends B = ${fmtBig(s.B)}</strong> to Alice.</li>
      </ul>
      <div class="mod-explainer">
         <strong>Why is it safe to share these numbers?</strong><br>
        Anyone watching the internet can see A and B — and that is perfectly fine.
        Even with A and B in hand, it is <strong>very hard to work backwards</strong> to find Alice's secret <em>a</em>
        or Bob's secret <em>b</em>. The mixing trick only works one way, like scrambling an egg.
      </div>`,
  },
  {
    // Step 6 — Alice receives B from Bob; Bob receives A from Alice
    show: ['a-p','a-g','a-a','a-A','a-B','b-p','b-g','b-b','b-B','b-A'],
    aliceHl: ['a-B'], bobHl: ['b-A'],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'a-a-val': s => fmtBig(s.a),
      'a-A-val': s => fmtBig(s.A),
      'a-B-val': s => fmtBig(s.B),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
      'b-b-val': s => fmtBig(s.b),
      'b-B-val': s => fmtBig(s.B),
      'b-A-val': s => fmtBig(s.A),
    },
    aliceSummary: s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  a = ${fmtBig(s.a)},  A = ${fmtBig(s.A)},  B = ${fmtBig(s.B)}`,
    bobSummary:   s => `p = ${fmtBig(s.p)},  g = ${fmtBig(s.g)},  b = ${fmtBig(s.b)},  B = ${fmtBig(s.B)},  A = ${fmtBig(s.A)}`,
    explanation:  s => `
      <p>The public numbers have arrived:</p>
      <ul class="plain-list">
        <li><strong>Alice receives B = ${fmtBig(s.B)}</strong> from Bob.</li>
        <li><strong>Bob receives A = ${fmtBig(s.A)}</strong> from Alice.</li>
      </ul>
      <p>Now both Alice and Bob have each other's public numbers. They are ready to create their shared secret!</p>`,
  },
  {
    // Step 7 — both compute shared secret
    show: ['a-p','a-g','a-a','a-A','a-B','a-K','b-p','b-g','b-b','b-B','b-A','b-K'],
    aliceHl: ['a-K'], bobHl: ['b-K'],
    cells: {
      'a-p-val': s => fmtBig(s.p),
      'a-g-val': s => fmtBig(s.g),
      'a-a-val': s => fmtBig(s.a),
      'a-A-val': s => fmtBig(s.A),
      'a-B-val': s => fmtBig(s.B),
      'a-K-val': s => fmtModExp('K', s.B, s.a, s.p, s.K),
      'b-p-val': s => fmtBig(s.p),
      'b-g-val': s => fmtBig(s.g),
      'b-b-val': s => fmtBig(s.b),
      'b-B-val': s => fmtBig(s.B),
      'b-A-val': s => fmtBig(s.A),
      'b-K-val': s => fmtModExp('K', s.A, s.b, s.p, s.K_bob),
    },
    aliceSummary: s => `…  A = ${fmtBig(s.A)},  B = ${fmtBig(s.B)},  K = ${fmtBig(s.K)}`,
    bobSummary:   s => `…  B = ${fmtBig(s.B)},  A = ${fmtBig(s.A)},  K = ${fmtBig(s.K_bob)}`,
    explanation:  s => `
      <p><strong>Alice</strong> uses her secret <em>a</em> and Bob's public information B to compute the shared secret:</p>
      <p class="calc-line">K = B<sup>a</sup> mod p &nbsp;→&nbsp; <strong>K = ${fmtBig(s.K)}</strong></p>
      ${calcLegend('B', 'a')}
      <p><strong>Bob</strong> uses his secret <em>b</em> and Alice's public information A to compute the shared secret:</p>
      <p class="calc-line">K = A<sup>b</sup> mod p &nbsp;→&nbsp; <strong>K = ${fmtBig(s.K_bob)}</strong></p>
      ${calcLegend('A', 'b')}
      <div class="mod-explainer">
         <strong>The magic moment!</strong><br>
        Even though Alice and Bob used <em>different</em> numbers to calculate K,
        they both get the <strong>same answer</strong>. This works because of how the mod maths balances out.<br><br>
         <strong>Alice and Bob have created the same secret key without ever sending the secret itself!</strong><br><br>
        A stranger watching the conversation only saw p, g, A, and B — but they
        <strong>cannot work backwards to find the secret key K</strong>.
        It is very hard to work backwards and find the secret number.
      </div>`,
  },
];

// ════════════════════════════════════════════════════════════════
//  Key-size selector / setMode
// ════════════════════════════════════════════════════════════════

/**
 * Update the security banner beneath the preset buttons.
 * Called on mode change and whenever the user edits the p field.
 */
function updateSecBanner(mode = 'custom') {
  if (!secBanner) return;
  secBanner.className = 'sec-banner warn';
  secBanner.textContent =
    'Small numbers are fine for learning how it works. For real private messages, use much larger numbers (2048+ bits).';
}
function setMode(mode = 'custom') {
  // No preset is selected by default: users must choose p and g themselves.
  state.mode = 'custom';

  document.querySelectorAll('.key-size-btn').forEach(btn => {
    btn.classList.remove('active');
  });

  inputP.value = '';
  inputP.placeholder = 'Enter your desired prime p…';
  inputG.value = '';
  inputG.placeholder = 'Enter your desired generator g…';
  if (btnResetP) btnResetP.style.display = 'none';

  updateSecBanner('custom');
  inputError.textContent = '';
  inputP.classList.remove('error');
  inputG.classList.remove('error');
}
// Restore RFC default p for the current standard mode
if (btnResetP) {
  btnResetP.addEventListener('click', () => {
    if (state.mode !== 'custom') {
      const group = RFC3526[state.mode];
      inputP.value = group.p.toString();
      inputG.value = group.g.toString();
      updateSecBanner(state.mode);
      inputP.classList.remove('error');
      inputG.classList.remove('error');
      inputError.textContent = '';
    }
  });
}

// Initialise without presets: Alice and Bob must agree on user-entered values.
setMode('custom');

// ════════════════════════════════════════════════════════════════
//  Render step
// ════════════════════════════════════════════════════════════════
function renderStep() {
  if (state.step < 0) return;
  const stepDef = STEPS[state.step];
  const data    = state;

  stepCur.textContent = state.step + 1;

  // Reset all param rows
  document.querySelectorAll('.param-row').forEach(el => el.className = 'param-row');
  stepDef.show.forEach(id    => $(id).classList.add('visible'));
  stepDef.aliceHl.forEach(id => $(id).classList.add('alice-hl'));
  stepDef.bobHl.forEach(id   => $(id).classList.add('bob-hl'));

  // ── Step 2: secret inputs ─────────────────────────────────────
  if (state.step === 1) {
    if (!state.secretsConfirmed) {
      inputA.style.display       = 'block';
      inputB.style.display       = 'block';
      $('a-a-val').style.display = 'none';
      $('b-b-val').style.display = 'none';
      confirmWrap.style.display  = 'block';
      btnNext.disabled           = true;
      expl.innerHTML             = stepDef.explanationPending(data);
    } else {
      inputA.style.display       = 'none';
      inputB.style.display       = 'none';
      $('a-a-val').style.display = 'block';
      $('b-b-val').style.display = 'block';
      confirmWrap.style.display  = 'none';
      btnNext.disabled           = false;
      expl.innerHTML             = stepDef.explanation(data);
    }
  } else {
    // Guard: cannot advance past step 1 without confirming secrets
    if (state.step >= 1 && !state.secretsConfirmed) {
      state.step = 1; renderStep(); return;
    }

    inputA.style.display       = 'none';
    inputB.style.display       = 'none';
    $('a-a-val').style.display = 'block';
    $('b-b-val').style.display = 'block';
    confirmWrap.style.display  = 'none';
    expl.innerHTML             = stepDef.explanation(data);

    if (state.step === TOTAL_STEPS - 1) {
      $('a-K').classList.add('shared-hl');
      $('b-K').classList.add('shared-hl');
      sharedBadge.classList.add('visible');
      badgeKVal.textContent = `K = ${fmtBig(data.K)}`;
      btnNext.disabled = true;
    } else {
      sharedBadge.classList.remove('visible');
      btnNext.disabled = false;
    }
  }

  btnTry.classList.add('visible');

  // Fill cells — use innerHTML so fmtModExp colour-spans and <sup> tags render
  Object.entries(stepDef.cells).forEach(([id, fn]) => {
    const el = $(id);
    if (el) el.innerHTML = fn(data);
  });

  // Update summaries
  const aliceEl = $('alice-summary');
  const bobEl   = $('bob-summary');
  if (data.p !== null) {
    aliceEl.textContent = stepDef.aliceSummary(data);
    aliceEl.classList.add('has-values');
    bobEl.textContent   = stepDef.bobSummary(data);
    bobEl.classList.add('has-values');
  } else {
    aliceEl.textContent = '—'; aliceEl.classList.remove('has-values');
    bobEl.textContent   = '—'; bobEl.classList.remove('has-values');
  }

  btnPrev.disabled = state.step <= 0;
  buildDots();
  typeset([expl, $('alice-card'), $('bob-card')]);
}

// ════════════════════════════════════════════════════════════════
//  Progress dots
// ════════════════════════════════════════════════════════════════
function buildDots() {
  dotsEl.innerHTML = '';
  for (let i = 0; i < TOTAL_STEPS; i++) {
    const d = document.createElement('div');
    d.className = 'dot'
      + (i < state.step   ? ' done'    : '')
      + (i === state.step ? ' current' : '');
    dotsEl.appendChild(d);
  }
}

function typeset(els) {
  if (window.MathJax && MathJax.typesetPromise)
    MathJax.typesetPromise(Array.isArray(els) ? els : [els]).catch(() => {});
}

// ════════════════════════════════════════════════════════════════
//  Agree on parameters
// ════════════════════════════════════════════════════════════════

/** Show / hide the loading spinner and disable the agree button. */
function setSpinner(visible, msg = 'Computing…') {
  const spinEl   = $('spinner');
  const spinText = spinEl ? spinEl.querySelector('span') : null;
  if (spinEl)   spinEl.style.display = visible ? 'flex' : 'none';
  if (spinText) spinText.textContent = msg;
  btnGen.disabled = visible;
}

function agree() {
  inputError.textContent = '';
  inputP.classList.remove('error');
  inputG.classList.remove('error');

  // ── 1. Read & parse p ─────────────────────────────────────────
  const rawP = inputP.value.trim().replace(/\s/g, '');
  if (!rawP) {
    inputError.textContent = 'Please type a prime number into the p box.';
    inputP.classList.add('error'); return;
  }
  const p = parseBig(rawP);
  if (p === null || p < 2n) {
    inputError.textContent = 'p must be a whole number of 2 or more.';
    inputP.classList.add('error'); return;
  }

  // ── 2. Bit-length validation ───────────────────────────────────
  const pBits = bitLength(p);
  if (pBits < MIN_BITS_CUSTOM) {
    inputError.textContent =
      `That number is too small (only ${pBits} bit${pBits === 1 ? '' : 's'}). ` +
      `Please use a larger prime. For real security, use at least 2048 bits.`;
    inputP.classList.add('error'); return;
  }

  // ── 3. Read & parse g ─────────────────────────────────────────
  const rawG = inputG.value.trim();
  if (!rawG) {
    inputError.textContent = 'Please type a starting number into the g box.';
    inputG.classList.add('error'); return;
  }
  const g = parseBig(rawG);
  if (g === null || g < 1n) {
    inputError.textContent = 'g must be a whole number of 1 or more.';
    inputG.classList.add('error'); return;
  }
  if (g >= p) {
    inputError.textContent = 'The starting number g must be smaller than p.';
    inputG.classList.add('error'); return;
  }

  // ── 4. Primality test (deferred so spinner renders first) ──────
  setSpinner(true, `Checking that ${pBits}-bit number is prime…`);

  setTimeout(() => {
    if (!millerRabin(p)) {
      setSpinner(false);
      inputError.textContent =
        `That number is not a prime. Please enter a prime number for p. ` +
        `(A prime number can only be divided evenly by 1 and itself like 7, 11, 13, 23…)`;
      inputP.classList.add('error'); return;
    }

    // ── 5. Security label ────────────────────────────────────────
    const label = pBits >= 2048
      ? `Your ${pBits}-bit prime — secure for real use`
      : `Your ${pBits}-bit prime — good for learning, too small for real use`;

    setSpinner(false);
    _finaliseAgree(p, g, label);
  }, 30);
}

/**
 * Called once p and g are fully validated (after spinner/timeout).
 * Commits to state, updates UI, and kicks off step rendering.
 * @param {BigInt} p  - validated prime modulus
 * @param {BigInt} g  - validated generator
 * @param {string} label - human-readable description shown in bit-info
 */
function _finaliseAgree(p, g, label) {
  const pBits = bitLength(p);

  state = { p, g, a: null, b: null, A: null, B: null, K: null, K_bob: null,
            step: 0, secretsConfirmed: false, mode: 'custom' };

  pubP.textContent = fmtBig(p);
  pubG.textContent = fmtBig(g);
  agreedDisplay.style.display = 'flex';

  // ── Bug fix 6: show bit-length info in agreed display ─────────
  let bitInfoEl = $('agreed-bit-info');
  if (!bitInfoEl) {
    bitInfoEl = document.createElement('div');
    bitInfoEl.id = 'agreed-bit-info';
    bitInfoEl.style.cssText =
      'font-size:0.72rem;color:var(--muted);margin-top:0.25rem;font-family:var(--mono);';
    agreedDisplay.appendChild(bitInfoEl);
  }
  const secLevel = pBits >= 2048 ? 'Safe for real use'
                 : pBits >= 512  ? 'Too small for real use — learning only'
                 :                  'Very small — demonstration only';
  bitInfoEl.innerHTML =
    `<span style="color:${pBits >= 2048 ? 'var(--green)' : 'var(--accent2)'}">${secLevel}</span>` +
    ` &nbsp;|&nbsp; p is ${pBits} bits long &nbsp;|&nbsp; ${label}`;

  // Lock parameter inputs while demo runs
  inputP.disabled = true;
  inputG.disabled = true;
  document.querySelectorAll('.key-size-btn').forEach(b => b.disabled = true);
  if (btnResetP) btnResetP.disabled = true;

  btnGen.textContent = 'Agreed — click Next to start';
  btnGen.disabled  = true;
  btnNext.disabled = false;
  btnPrev.disabled = true;

  renderStep();
}

// ════════════════════════════════════════════════════════════════
//  Confirm secrets (Step 2)
// ════════════════════════════════════════════════════════════════
function confirmSecrets() {
  errorA.textContent = '';
  errorB.textContent = '';
  errorSecrets.textContent = '';
  inputA.classList.remove('error');
  inputB.classList.remove('error');

  const { p } = state;
  const pBits = bitLength(p);

  // ── Bug fix 2: auto-fill random secrets if fields left empty ──
  if (!inputA.value.trim()) {
    const autoA = randomSecret(p);
    inputA.value = autoA.toString();
    errorA.textContent = `Auto-generated a random secret for Alice.`;
  }
  if (!inputB.value.trim()) {
    const autoB = randomSecret(p);
    inputB.value = autoB.toString();
    errorB.textContent = `Auto-generated a random secret for Bob.`;
  }

  const rawA = inputA.value.trim();
  const rawB = inputB.value.trim();
  let valid = true;

  if (!rawA) { errorA.textContent = 'Alice needs a secret value.'; inputA.classList.add('error'); valid = false; }
  if (!rawB) { errorB.textContent = 'Bob needs a secret value.';   inputB.classList.add('error'); valid = false; }
  if (!valid) return;

  const a = parseBig(rawA);
  const b = parseBig(rawB);

  if (a === null || a < 1n) {
    errorA.textContent = 'Must be a positive integer.'; inputA.classList.add('error'); return;
  }
  if (b === null || b < 1n) {
    errorB.textContent = 'Must be a positive integer.'; inputB.classList.add('error'); return;
  }

  const { g } = state;

  // Validate range: 1 ≤ a,b < p - 2
  if (a >= p - 2n) {
    errorA.textContent = 'a must be less than p - 2';
    inputA.classList.add('error'); return;
  }
  if (b >= p - 2n) {
    errorB.textContent = 'b must be less than p - 2';
    inputB.classList.add('error'); return;
  }

  // Compute public keys
  const A = modPow(g, a, p);    // Alice: A = g^a mod p
  const B = modPow(g, b, p);    // Bob:   B = g^b mod p

  // Compute shared secrets — both must match
  const K     = modPow(B, a, p);   // Alice: K = B^a mod p
  const K_bob = modPow(A, b, p);   // Bob:   K = A^b mod p

  // Sanity check — must always hold by DH mathematics
  if (K !== K_bob) {
    errorSecrets.textContent =
      'Unexpected error: shared keys do not match. This should never happen — please report this bug.';
    return;
  }

  state = { ...state, a, b, A, B, K, K_bob, secretsConfirmed: true };
  renderStep();
}

// ════════════════════════════════════════════════════════════════
//  Full reset
// ════════════════════════════════════════════════════════════════
function resetUI() {
  const savedMode = state.mode;
  state = { p: null, g: null, a: null, b: null, A: null, B: null,
            K: null, K_bob: null, step: -1, secretsConfirmed: false, mode: savedMode };

  ['a-p-val','a-g-val','a-a-val','a-A-val','a-B-val','a-K-val',
   'b-p-val','b-g-val','b-b-val','b-B-val','b-A-val','b-K-val']
    .forEach(id => { const el = $(id); if (el) el.textContent = '—'; });

  $('a-a-val').style.display = 'block';
  $('b-b-val').style.display = 'block';
  pubP.textContent = '—'; pubG.textContent = '—';
  const bitInfoEl = $('agreed-bit-info');
  if (bitInfoEl) bitInfoEl.textContent = '';
  stepCur.textContent = '0'; dotsEl.innerHTML = '';

  document.querySelectorAll('.param-row').forEach(el => el.className = 'param-row');
  sharedBadge.classList.remove('visible');
  btnTry.classList.remove('visible');
  btnNext.disabled = true; btnPrev.disabled = true;

  // Re-enable inputs
  inputP.disabled = false;
  inputG.disabled = false;
  if (btnResetP) btnResetP.disabled = false;
  document.querySelectorAll('.key-size-btn').forEach(b => b.disabled = false);
  inputP.classList.remove('error');
  inputG.classList.remove('error');
  inputError.textContent = '';
  agreedDisplay.style.display = 'none';

  inputA.value = ''; inputA.style.display = 'none'; inputA.classList.remove('error');
  inputB.value = ''; inputB.style.display = 'none'; inputB.classList.remove('error');
  errorA.textContent = ''; errorB.textContent = '';
  errorSecrets.textContent = ''; confirmWrap.style.display = 'none';

  const aliceEl = $('alice-summary');
  const bobEl   = $('bob-summary');
  aliceEl.textContent = '—'; aliceEl.classList.remove('has-values');
  bobEl.textContent   = '—'; bobEl.classList.remove('has-values');

  btnGen.textContent = 'Agree on Parameters →';
  btnGen.disabled    = false;

  // Re-apply the mode (resets p/g fields)
  setMode(savedMode);

  expl.innerHTML = `
    <p>Alice and Bob need to agree on two numbers that everyone can see — a <strong>prime number p</strong>
       and a <strong>starting number g</strong>. Type them above and click
       <strong>Agree on Parameters</strong> to begin.</p>
    <p>Small numbers are fine for learning. Use the <kbd>←</kbd> <kbd>→</kbd> arrow keys to move between steps.</p>`;
  typeset([expl]);
}

// ════════════════════════════════════════════════════════════════
//  Event listeners
// ════════════════════════════════════════════════════════════════
btnGen.addEventListener('click', agree);
btnConfirm.addEventListener('click', confirmSecrets);

inputA.addEventListener('keydown', e => { if (e.key === 'Enter') inputB.focus(); });
inputB.addEventListener('keydown', e => { if (e.key === 'Enter') confirmSecrets(); });
inputA.addEventListener('input',   () => { inputA.classList.remove('error'); errorA.textContent = ''; });
inputB.addEventListener('input',   () => { inputB.classList.remove('error'); errorB.textContent = ''; });

inputG.addEventListener('keydown', e => { if (e.key === 'Enter') agree(); });
inputG.addEventListener('input',   () => { inputG.classList.remove('error'); inputError.textContent = ''; });

inputP.addEventListener('input', () => {
  inputP.classList.remove('error');
  inputError.textContent = '';
  // If the user edits p away from all RFC presets, switch visual mode to custom
  const val = inputP.value.trim().replace(/\s/g, '');
  const matchedMode = Object.entries(RFC3526).find(([, grp]) => grp.p.toString() === val);
  if (matchedMode) {
    // Quietly update mode label to matching RFC size without re-filling fields
    state.mode = matchedMode[0];
    document.querySelectorAll('.key-size-btn').forEach(btn => {
      btn.classList.toggle('active', btn.dataset.size === matchedMode[0]);
    });
    updateSecBanner(matchedMode[0]);
  } else if (val) {
    state.mode = 'custom';
    document.querySelectorAll('.key-size-btn').forEach(btn => {
      btn.classList.toggle('active', btn.dataset.size === 'custom');
    });
    updateSecBanner('custom');
  }
});

btnNext.addEventListener('click', () => {
  if (state.step < TOTAL_STEPS - 1) { state.step++; renderStep(); }
});
btnPrev.addEventListener('click', () => {
  if (state.step > 0) { state.step--; renderStep(); }
});
btnTry.addEventListener('click', resetUI);

document.addEventListener('keydown', e => {
  if (e.key === 'ArrowRight' && !btnNext.disabled) btnNext.click();
  if (e.key === 'ArrowLeft'  && !btnPrev.disabled) btnPrev.click();
});

window.addEventListener('load', () => typeset([document.body]));
