#include <iostream>
#include <atomic>
#include <mutex>
#include <thread>
#include <chrono>
#include <vector>
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <cassert>
#include "pointer_with_mutex.hpp"
#include "one_byte_mutex.hpp"

struct AssertingMutex
{
	AssertingMutex()
		: is_in_use(0)
	{
	}

	void lock()
	{
		assert(++is_in_use == 1);
	}
	void unlock()
	{
		assert(--is_in_use == 0);
	}

private:
	std::atomic<signed char> is_in_use;
};


template<typename Mutex>
void lock_in_loop(Mutex & mutex, AssertingMutex & asserter, int count)
{
	for (int i = 0; i < count; ++i)
	{
		mutex.lock();
		//asserter.lock();
		//asserter.unlock();
		mutex.unlock();
	}
}

template<typename Mutex>
auto measure(Mutex & mutex)
{
	AssertingMutex asserter;
	int count = 1024 * 1024;
	std::vector<std::thread> threads;
	threads.reserve(std::thread::hardware_concurrency());
	//threads.reserve(1);
	auto before = std::chrono::high_resolution_clock::now();
	while (threads.size() != threads.capacity())
	{
		threads.emplace_back([&]
		{
			lock_in_loop(mutex, asserter, count);
		});
	}
	for (std::thread& t : threads)
		t.join();
	return std::chrono::high_resolution_clock::now() - before;
}

int main()
{
	std::chrono::nanoseconds time_spent;
	switch (2)
	{
	case 1:
	{
		std::mutex mutex;
		time_spent = measure(mutex);
		break;
	}
	case 2:
	{
		one_byte_mutex mutex;
		time_spent = measure(mutex);
		break;
	}
	case 3:
	{
		int point_at_me = 5;
		pointer_with_mutex<int> mutex;
		mutex.lock();
		mutex.set(&point_at_me);
		assert(*mutex.get() == 5);
		mutex.unlock();
		time_spent = measure(mutex);
	}
	}
	std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(time_spent).count() << "ms" << std::endl;
	//assert(*mutex.get() == 5);
}
