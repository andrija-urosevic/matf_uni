lst = [int(it) for it in input().split(',')]

n = len(lst)
k = 0
for i in range(n - 1):
    if lst[i] > lst[i + 1]:
        k = i + 1
        break

print(lst[k:] + lst[:k])
