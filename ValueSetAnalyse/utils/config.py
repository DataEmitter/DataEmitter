from copy import deepcopy

DEBUG = True

MAX_INPUT_LEN = 50

RANDOM_INPUT = True
word_list=[
    '5',
    '\n',
    '1',
    '2',
    '3',
    '4',
    '6',
]

std_input = [
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
]

back_std_input = deepcopy(std_input)
std_file_input = [
    
    'FILE INPUT LINE'
]

std_input.reverse()
std_file_input.reverse()