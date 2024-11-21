const go = {
  _types: Object.create(),

  string: (v) => v,
  bool: (v) => v,
  int: (v) => Number(new BigInt64Array([BigInt(v)])[0]),
  int64: (v) => Number(new BigInt64Array([BigInt(v)])[0]),
  int8: (v) => new Int8Array([v])[0],
  int16: (v) => new Int16Array([v])[0],
  int32: (v) => new Int32Array([v])[0],
  uint: (v) => Number(new BigUint64Array([BigInt(v)])[0]),
  uint64: (v) => Number(new BigUint64Array([BigInt(v)])[0]),
  uint8: (v) => new Uint8Array([v])[0],
  uint16: (v) => new Uint16Array([v])[0],
  uint32: (v) => new Uint32Array([v])[0],
  float32: (v) => new Float32Array([v])[0],
  float64: (v) => new Float64Array([v])[0],
  toIface(v, type) {
    return {
      type: type,
      data: go.ref(v),
    };
  },
  typeAssert(v, type) {
    const { vType, vData } = v;
    const ok = vType === type;
    return {
      v: ok ? vData : undefined,
      ok: ok,
    };
  },
  ref(v) {
    return {
      v: v,
      unref() {
        return this.v;
      },
      store(v) {
        this.v = v;
        return this;
      },
    };
  },
  sliceFromArray(arr) {
    return Object.create({
      offset: 0,
      len: arr ? arr.length : 0,
      cap: arr ? arr.length : 0,
      data: go.ref(arr),
    });
  },
  sliceToArray(s) {
    return s.data.unref().slice(s.offset, s.offset + s.len);
  },
  len(v) {
    return v.len;
  },
  cap(v) {
    return v.cap;
  },
  makeslice(zero, len, cap) {
    len = len || 0;
    cap = cap || 0;
    if (len < 0) {
      throw new Error("makeslice: len out of range");
    }

    if (len > cap || cap < 0) {
      throw new Error("makeslice: cap out of range");
    }

    return Object.create({
      offset: 0,
      len: len,
      cap: cap,
      data: go.ref(Array(cap).fill(zero)),
    });
  },
  slice(s, low, high, max) {
    let { len, cap, data } = s;
    if (low < 0) {
      throw new Error(`slice bounds out of range [${low}:]`);
    }
    if (high < 0) {
      throw new Error(`slice bounds out of range [:${high}]`);
    }
    if (max < 0) {
      throw new Error(`slice bounds out of range [::${max}]`);
    }

    if (low > high) {
      throw new Error(`slice bounds out of range [${low}:${high}]`);
    }
    if (high > max) {
      throw new Error(`slice bounds out of range [:${high}:${max}]`);
    }

    if (high > cap) {
      throw new Error(
        `slice bounds out of range [:${high}] with capacity ${cap}`
      );
    }

    if (high === undefined) {
      high = len;
    }
    if (low === undefined) {
      low = 0;
    }

    len = high - low;
    if (max !== undefined) {
      cap = max;
    }

    return Object.create({
      offset: low,
      len: len,
      cap: cap,
      data: data,
    });
  },
};
