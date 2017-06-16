
#ifndef _FIXED_SIZE_STACK_H
#define _FIXED_SIZE_STACK_H

template <typename T>
class FixedSizeStack
{
	private:
		int capacity;
		int topPtr;
		T *stack;
	public:
		FixedSizeStack(int capacity)
		{
			this->capacity = capacity;
			topPtr = 0;
			stack = new T[capacity + 1];
		}

		bool empty() { return (topPtr == 0); }
		void push(const T &element) { assert(topPtr < capacity); stack[topPtr++] = element; }
		void pop() { assert(topPtr > 0); topPtr--; }
		void clear() { topPtr = 0; }

		int size() { return top; }
		T top() const { assert(topPtr > 0); return stack[topPtr - 1]; }
};

#endif
