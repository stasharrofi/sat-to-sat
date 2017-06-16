#ifndef _FIXED_SIZE_INT_SET_H_
#define _FIXED_SIZE_INT_SET_H_

#include <cstring>
#include <assert.h>
#include <boost/dynamic_bitset.hpp>

class VoidTrait
{
	protected:
		VoidTrait(int) {}
		void insertElement(int) {}
		void removeElement(int) {}
		void clearElements() {}
};

class CountabilityTrait
{
	private:
		int sz;

	protected:
		CountabilityTrait(int) : sz(0) {}
		void insertElement(int) { ++sz; }
		void removeElement(int) { --sz; }
		void clearElements() { sz = 0; }

	public:
		int size() { return sz; }
};

class EnumerabilityTrait
{
	private:
		int start, capacity;
		int *next;
		int *prev;

	protected:
		EnumerabilityTrait(int cap)
		{
			start = -1;
			capacity = cap;
			next = new int[capacity];
			prev = new int[capacity];
		}

		void insertElement(int n)
		{
			next[n] = start;
			prev[n] = -1;
			if (start >= 0)
				prev[start] = n;
			start = n;
		}

		void removeElement(int n)
		{
			if (next[n] >= 0)
				prev[next[n]] = prev[n];
			if (prev[n] >= 0)
				next[prev[n]] = next[n];
			else
				start = next[n];
		}

		void clearElements()
		{
			start = -1;
		}

	public:
		int begin() { return start; }
		int end() { return -1; }
		int nextNumber(int curNumber) { assert((curNumber >= 0) && (curNumber < capacity)); return next[curNumber]; }
};

template <typename Trait>
class FixedSizeIntSet : public Trait
{
	private:
		//const int MAX_TAG = 1000000000;
		int cap;
		//int currentTag;
		//uint32_t *tags;
		boost::dynamic_bitset<> internalSet;

		//void initialize() { memset(tags, 0, ((capacity + 31) >> 5) * sizeof(uint32_t)); }
	public:
		FixedSizeIntSet(int cap) : Trait(cap), internalSet(cap)
		{
			this->cap = cap;
			//this->currentTag = 1;
			//tags = new int[capacity];
			//initialize();
		}

		void insert(int n)
		{
			assert((n >= 0) && (n < cap));
			//if (tags[n] != currentTag)
			if (!internalSet[n])
				Trait::insertElement(n);
			//tags[n] = currentTag;
			internalSet.set(n);
		}

		void remove(int n)
		{
			if ((n >= 0) && (n < cap))
			{
				//if (tags[n] == currentTag) 
				if (internalSet[n])
					Trait::removeElement(n);

				//tags[n] = 0;
				internalSet.reset(n);
			}
		}

		void clear()
		{
			//if (currentTag < MAX_TAG)
			//	currentTag++;
			//else { initialize(); currentTag = 1; }
			Trait::clearElements();
			//initialize();
			internalSet.reset();
		}

//		bool hasMember(int n) { return ((n >= 0) && (n < capacity)) ? (currentTag == tags[n]) : false; }
		bool hasMember(int n) { return ((n >= 0) && (n < cap)) ? internalSet.test(n) : false; }

		int capacity() { return cap; }
};

#endif
