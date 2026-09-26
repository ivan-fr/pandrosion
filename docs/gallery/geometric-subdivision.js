// The construction uses arithmetic and square roots only; no real power or logarithm.
export function subdivide(X, p, n) {
  if (!Number.isFinite(X) || X <= 1 || X > 1e12 || !Number.isFinite(p) || p < 1 || p > 1e12 || !Number.isInteger(n) || n < 0 || n > 24) throw new RangeError('Use 1 < X ≤ 10¹², 1 ≤ p ≤ 10¹² and 0 ≤ n ≤ 24.');
  const theta = 1 / p;
  let a = 0, b = 1, A = 1, B = X;
  const history = [];
  for (let i = 0; i < n; i++) {
    const m = (a + b) / 2, M = Math.sqrt(A) * Math.sqrt(B);
    history.push({a, b, A, B, m, M, left: theta <= m});
    if (theta <= m) { b = m; B = M; } else { a = m; A = M; }
  }
  const lambda = Math.max(0, Math.min(1, (theta - a) / (b - a)));
  const U = (1 - lambda) * A + lambda * B;
  const L = A / ((1 - lambda) + lambda * (A / B));
  const width = lambda * (1 - lambda) * ((B - A) / A) * ((B - A) / B);
  return {X, p, n, theta, a, b, A, B, lambda, U, L, width, history};
}
