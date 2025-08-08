#include "stdio.h"

#define SIZE 5

int main() {
  int dst[SIZE];
  int a[SIZE] = {1, 2, 3, 4, 5};
  int b[SIZE] = {6, 7, 8, 9, 10};
  for (int i = 0; i < SIZE; ++i) {
    dst[i] = a[i] + b[i];
  }
    printf("dst[0] = %d\n", dst[0]);
    printf("dst[1] = %d\n", dst[1]);
    printf("dst[2] = %d\n", dst[2]);
    printf("dst[3] = %d\n", dst[3]);
    printf("dst[4] = %d\n", dst[4]);
}