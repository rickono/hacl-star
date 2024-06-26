#pragma once

typedef struct
{
  uint8_t* input;
  size_t input_len;
  uint8_t tag_224[28];
  uint8_t tag_256[32];
  uint8_t tag_384[48];
  uint8_t tag_512[64];
} sha2_test_vector;

static uint8_t input1[] = { 0x61U, 0x62U, 0x63U };

static uint8_t input2[] = {};

static uint8_t input3[] = { 0x61U, 0x62U, 0x63U, 0x64U, 0x62U, 0x63U, 0x64U,
                            0x65U, 0x63U, 0x64U, 0x65U, 0x66U, 0x64U, 0x65U,
                            0x66U, 0x67U, 0x65U, 0x66U, 0x67U, 0x68U, 0x66U,
                            0x67U, 0x68U, 0x69U, 0x67U, 0x68U, 0x69U, 0x6aU,
                            0x68U, 0x69U, 0x6aU, 0x6bU, 0x69U, 0x6aU, 0x6bU,
                            0x6cU, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6bU, 0x6cU,
                            0x6dU, 0x6eU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x6dU,
                            0x6eU, 0x6fU, 0x70U, 0x6eU, 0x6fU, 0x70U, 0x71U };

static uint8_t input4[] = {
  0x61U, 0x62U, 0x63U, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U, 0x62U, 0x63U, 0x64U,
  0x65U, 0x66U, 0x67U, 0x68U, 0x69U, 0x63U, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U,
  0x69U, 0x6aU, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x65U,
  0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x66U, 0x67U, 0x68U, 0x69U,
  0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6dU,
  0x6eU, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x69U, 0x6aU,
  0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU,
  0x6fU, 0x70U, 0x71U, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U,
  0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x6dU, 0x6eU, 0x6fU,
  0x70U, 0x71U, 0x72U, 0x73U, 0x74U, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x73U,
  0x74U, 0x75U
};

static sha2_test_vector vectors[] = {
  { .input = input1,
    .input_len = sizeof(input1),
    .tag_224 = { 0x23U, 0x09U, 0x7dU, 0x22U, 0x34U, 0x05U, 0xd8U,
                 0x22U, 0x86U, 0x42U, 0xa4U, 0x77U, 0xbdU, 0xa2U,
                 0x55U, 0xb3U, 0x2aU, 0xadU, 0xbcU, 0xe4U, 0xbdU,
                 0xa0U, 0xb3U, 0xf7U, 0xe3U, 0x6cU, 0x9dU, 0xa7U },
    .tag_256 = { 0xbaU, 0x78U, 0x16U, 0xbfU, 0x8fU, 0x01U, 0xcfU, 0xeaU,
                 0x41U, 0x41U, 0x40U, 0xdeU, 0x5dU, 0xaeU, 0x22U, 0x23U,
                 0xb0U, 0x03U, 0x61U, 0xa3U, 0x96U, 0x17U, 0x7aU, 0x9cU,
                 0xb4U, 0x10U, 0xffU, 0x61U, 0xf2U, 0x00U, 0x15U, 0xadU },
    .tag_384 = { 0xcbU, 0x00U, 0x75U, 0x3fU, 0x45U, 0xa3U, 0x5eU, 0x8bU,
                 0xb5U, 0xa0U, 0x3dU, 0x69U, 0x9aU, 0xc6U, 0x50U, 0x07U,
                 0x27U, 0x2cU, 0x32U, 0xabU, 0x0eU, 0xdeU, 0xd1U, 0x63U,
                 0x1aU, 0x8bU, 0x60U, 0x5aU, 0x43U, 0xffU, 0x5bU, 0xedU,
                 0x80U, 0x86U, 0x07U, 0x2bU, 0xa1U, 0xe7U, 0xccU, 0x23U,
                 0x58U, 0xbaU, 0xecU, 0xa1U, 0x34U, 0xc8U, 0x25U, 0xa7U },
    .tag_512 = { 0xddU, 0xafU, 0x35U, 0xa1U, 0x93U, 0x61U, 0x7aU, 0xbaU,
                 0xccU, 0x41U, 0x73U, 0x49U, 0xaeU, 0x20U, 0x41U, 0x31U,
                 0x12U, 0xe6U, 0xfaU, 0x4eU, 0x89U, 0xa9U, 0x7eU, 0xa2U,
                 0x0aU, 0x9eU, 0xeeU, 0xe6U, 0x4bU, 0x55U, 0xd3U, 0x9aU,
                 0x21U, 0x92U, 0x99U, 0x2aU, 0x27U, 0x4fU, 0xc1U, 0xa8U,
                 0x36U, 0xbaU, 0x3cU, 0x23U, 0xa3U, 0xfeU, 0xebU, 0xbdU,
                 0x45U, 0x4dU, 0x44U, 0x23U, 0x64U, 0x3cU, 0xe8U, 0x0eU,
                 0x2aU, 0x9aU, 0xc9U, 0x4fU, 0xa5U, 0x4cU, 0xa4U, 0x9fU } },
  {
    .input = input2,
    .input_len = sizeof(input2),
    .tag_224 = { 0xd1U, 0x4aU, 0x02U, 0x8cU, 0x2aU, 0x3aU, 0x2bU,
                 0xc9U, 0x47U, 0x61U, 0x02U, 0xbbU, 0x28U, 0x82U,
                 0x34U, 0xc4U, 0x15U, 0xa2U, 0xb0U, 0x1fU, 0x82U,
                 0x8eU, 0xa6U, 0x2aU, 0xc5U, 0xb3U, 0xe4U, 0x2fU },
    .tag_256 = { 0xe3U, 0xb0U, 0xc4U, 0x42U, 0x98U, 0xfcU, 0x1cU, 0x14U,
                 0x9aU, 0xfbU, 0xf4U, 0xc8U, 0x99U, 0x6fU, 0xb9U, 0x24U,
                 0x27U, 0xaeU, 0x41U, 0xe4U, 0x64U, 0x9bU, 0x93U, 0x4cU,
                 0xa4U, 0x95U, 0x99U, 0x1bU, 0x78U, 0x52U, 0xb8U, 0x55U },
    .tag_384 = { 0x38U, 0xb0U, 0x60U, 0xa7U, 0x51U, 0xacU, 0x96U, 0x38U,
                 0x4cU, 0xd9U, 0x32U, 0x7eU, 0xb1U, 0xb1U, 0xe3U, 0x6aU,
                 0x21U, 0xfdU, 0xb7U, 0x11U, 0x14U, 0xbeU, 0x07U, 0x43U,
                 0x4cU, 0x0cU, 0xc7U, 0xbfU, 0x63U, 0xf6U, 0xe1U, 0xdaU,
                 0x27U, 0x4eU, 0xdeU, 0xbfU, 0xe7U, 0x6fU, 0x65U, 0xfbU,
                 0xd5U, 0x1aU, 0xd2U, 0xf1U, 0x48U, 0x98U, 0xb9U, 0x5bU },
    .tag_512 = { 0xcfU, 0x83U, 0xe1U, 0x35U, 0x7eU, 0xefU, 0xb8U, 0xbdU,
                 0xf1U, 0x54U, 0x28U, 0x50U, 0xd6U, 0x6dU, 0x80U, 0x07U,
                 0xd6U, 0x20U, 0xe4U, 0x05U, 0x0bU, 0x57U, 0x15U, 0xdcU,
                 0x83U, 0xf4U, 0xa9U, 0x21U, 0xd3U, 0x6cU, 0xe9U, 0xceU,
                 0x47U, 0xd0U, 0xd1U, 0x3cU, 0x5dU, 0x85U, 0xf2U, 0xb0U,
                 0xffU, 0x83U, 0x18U, 0xd2U, 0x87U, 0x7eU, 0xecU, 0x2fU,
                 0x63U, 0xb9U, 0x31U, 0xbdU, 0x47U, 0x41U, 0x7aU, 0x81U,
                 0xa5U, 0x38U, 0x32U, 0x7aU, 0xf9U, 0x27U, 0xdaU, 0x3eU },
  },
  { .input = input3,
    .input_len = sizeof(input3),
    .tag_224 = { 0x75U, 0x38U, 0x8bU, 0x16U, 0x51U, 0x27U, 0x76U,
                 0xccU, 0x5dU, 0xbaU, 0x5dU, 0xa1U, 0xfdU, 0x89U,
                 0x01U, 0x50U, 0xb0U, 0xc6U, 0x45U, 0x5cU, 0xb4U,
                 0xf5U, 0x8bU, 0x19U, 0x52U, 0x52U, 0x25U, 0x25U },
    .tag_256 = { 0x24U, 0x8dU, 0x6aU, 0x61U, 0xd2U, 0x06U, 0x38U, 0xb8U,
                 0xe5U, 0xc0U, 0x26U, 0x93U, 0x0cU, 0x3eU, 0x60U, 0x39U,
                 0xa3U, 0x3cU, 0xe4U, 0x59U, 0x64U, 0xffU, 0x21U, 0x67U,
                 0xf6U, 0xecU, 0xedU, 0xd4U, 0x19U, 0xdbU, 0x06U, 0xc1U },
    .tag_384 = { 0x33U, 0x91U, 0xfdU, 0xddU, 0xfcU, 0x8dU, 0xc7U, 0x39U,
                 0x37U, 0x07U, 0xa6U, 0x5bU, 0x1bU, 0x47U, 0x09U, 0x39U,
                 0x7cU, 0xf8U, 0xb1U, 0xd1U, 0x62U, 0xafU, 0x05U, 0xabU,
                 0xfeU, 0x8fU, 0x45U, 0x0dU, 0xe5U, 0xf3U, 0x6bU, 0xc6U,
                 0xb0U, 0x45U, 0x5aU, 0x85U, 0x20U, 0xbcU, 0x4eU, 0x6fU,
                 0x5fU, 0xe9U, 0x5bU, 0x1fU, 0xe3U, 0xc8U, 0x45U, 0x2bU },
    .tag_512 = { 0x20U, 0x4aU, 0x8fU, 0xc6U, 0xddU, 0xa8U, 0x2fU, 0x0aU,
                 0x0cU, 0xedU, 0x7bU, 0xebU, 0x8eU, 0x08U, 0xa4U, 0x16U,
                 0x57U, 0xc1U, 0x6eU, 0xf4U, 0x68U, 0xb2U, 0x28U, 0xa8U,
                 0x27U, 0x9bU, 0xe3U, 0x31U, 0xa7U, 0x03U, 0xc3U, 0x35U,
                 0x96U, 0xfdU, 0x15U, 0xc1U, 0x3bU, 0x1bU, 0x07U, 0xf9U,
                 0xaaU, 0x1dU, 0x3bU, 0xeaU, 0x57U, 0x78U, 0x9cU, 0xa0U,
                 0x31U, 0xadU, 0x85U, 0xc7U, 0xa7U, 0x1dU, 0xd7U, 0x03U,
                 0x54U, 0xecU, 0x63U, 0x12U, 0x38U, 0xcaU, 0x34U, 0x45U } },
  { .input = input4,
    .input_len = sizeof(input4),
    .tag_224 = { 0xc9U, 0x7cU, 0xa9U, 0xa5U, 0x59U, 0x85U, 0x0cU,
                 0xe9U, 0x7aU, 0x04U, 0xa9U, 0x6dU, 0xefU, 0x6dU,
                 0x99U, 0xa9U, 0xe0U, 0xe0U, 0xe2U, 0xabU, 0x14U,
                 0xe6U, 0xb8U, 0xdfU, 0x26U, 0x5fU, 0xc0U, 0xb3U },
    .tag_256 = { 0xcfU, 0x5bU, 0x16U, 0xa7U, 0x78U, 0xafU, 0x83U, 0x80U,
                 0x03U, 0x6cU, 0xe5U, 0x9eU, 0x7bU, 0x04U, 0x92U, 0x37U,
                 0x0bU, 0x24U, 0x9bU, 0x11U, 0xe8U, 0xf0U, 0x7aU, 0x51U,
                 0xafU, 0xacU, 0x45U, 0x03U, 0x7aU, 0xfeU, 0xe9U, 0xd1U },
    .tag_384 = { 0x09U, 0x33U, 0x0cU, 0x33U, 0xf7U, 0x11U, 0x47U, 0xe8U,
                 0x3dU, 0x19U, 0x2fU, 0xc7U, 0x82U, 0xcdU, 0x1bU, 0x47U,
                 0x53U, 0x11U, 0x1bU, 0x17U, 0x3bU, 0x3bU, 0x05U, 0xd2U,
                 0x2fU, 0xa0U, 0x80U, 0x86U, 0xe3U, 0xb0U, 0xf7U, 0x12U,
                 0xfcU, 0xc7U, 0xc7U, 0x1aU, 0x55U, 0x7eU, 0x2dU, 0xb9U,
                 0x66U, 0xc3U, 0xe9U, 0xfaU, 0x91U, 0x74U, 0x60U, 0x39U },
    .tag_512 = { 0x8eU, 0x95U, 0x9bU, 0x75U, 0xdaU, 0xe3U, 0x13U, 0xdaU,
                 0x8cU, 0xf4U, 0xf7U, 0x28U, 0x14U, 0xfcU, 0x14U, 0x3fU,
                 0x8fU, 0x77U, 0x79U, 0xc6U, 0xebU, 0x9fU, 0x7fU, 0xa1U,
                 0x72U, 0x99U, 0xaeU, 0xadU, 0xb6U, 0x88U, 0x90U, 0x18U,
                 0x50U, 0x1dU, 0x28U, 0x9eU, 0x49U, 0x00U, 0xf7U, 0xe4U,
                 0x33U, 0x1bU, 0x99U, 0xdeU, 0xc4U, 0xb5U, 0x43U, 0x3aU,
                 0xc7U, 0xd3U, 0x29U, 0xeeU, 0xb6U, 0xddU, 0x26U, 0x54U,
                 0x5eU, 0x96U, 0xe5U, 0x5bU, 0x87U, 0x4bU, 0xe9U, 0x09U } }
};
