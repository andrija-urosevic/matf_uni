import heapq

def heap_sort(lst):
    heap = lst
    heapq.heapify(heap)
    return [heapq.heappop(heap) for _ in range(len(heap))]

print(heap_sort([1,7,3,2,8,4,9,5]))
