const go = {
  string: (v) => v,
  bool: (v) => v,
  int: (v) => new BigInt64Array([v])[0],
  int64: (v) => new BigInt64Array([v])[0],
  int8: (v) => new Int8Array([v])[0],
  int16: (v) => new Int16Array([v])[0],
  int32: (v) => new Int32Array([v])[0],
  uint: (v) => new BigUint64Array([v])[0],
  uint64: (v) => new BigUint64Array([v])[0],
  uint8: (v) => new Uint8Array([v])[0],
  uint16: (v) => new Uint16Array([v])[0],
  uint32: (v) => new Uint32Array([v])[0],
  float32: (v) => new Float32Array([v])[0];
  float64: (v) => new Float64Array([v])[0],
};
