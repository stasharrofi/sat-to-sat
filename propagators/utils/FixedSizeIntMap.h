
#ifndef _FIXED_SIZE_INT_MAP_H_
#define _FIXED_SIZE_INT_MAP_H_

#include "FixedSizeIntSet.h"

template <typename T>
class FixedSizeIntMap
{
	private:
		FixedSizeIntSet<VoidTrait> keys;
		T *values;
	public:
		FixedSizeIntMap(int cap) : keys(cap) { values = new T[cap]; }

		int capacity() { return keys.capacity(); }
		void insert(int key, const T &value) { keys.insert(key); values[key] = value; }
		void remove(int key) { keys.remove(key); }
		void clear() { keys.clear(); }

		bool hasKey(int key) { return keys.hasMember(key); }
		const T &valueOf(int key) { assert((key >= 0) && (key < capacity())); return values[key]; }
};

#endif
