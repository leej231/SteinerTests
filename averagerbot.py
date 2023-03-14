import ast
import os, glob
path = 'C:\\pythonpractice\\New folder'
fnames = os.listdir(path)


filename = fnames[0]

with open(filename, 'r') as file:
   fileinfo = file.read().splitlines()

number_of_tests = len(ast.literal_eval(fileinfo[0]))

aa = [0] * number_of_tests
bb = [0] * number_of_tests
cc = [0] * number_of_tests
dd = [0] * number_of_tests
ee = [0] * number_of_tests

counter = 0

for filename in glob.glob(os.path.join(path, '*.txt')):
   counter += 1
   with open(os.path.join(os.getcwd(), filename), 'r') as f: # open in readonly mode
      # do your stuff
      fileinfo = f.read().splitlines()
      for i in range(number_of_tests):
         aa[i] += ast.literal_eval(fileinfo[0])[i]
         bb[i] += ast.literal_eval(fileinfo[1])[i]
         cc[i] += ast.literal_eval(fileinfo[2])[i]
         dd[i] += ast.literal_eval(fileinfo[3])[i]
         ee[i] += ast.literal_eval(fileinfo[4])[i]

line1 = [item/counter for item in aa]
line2 = [item/counter for item in bb]
line3 = [item/counter for item in cc]
line4 = [item/counter for item in dd]
line5 = [item/counter for item in ee]

print(line1,'\n',line2,'\n',line3,'\n',line4)

with open('average.txt', 'w+') as file:
   file.write(str(line1)+"\n")
   file.write(str(line2)+"\n")
   file.write(str(line3)+"\n")
   file.write(str(line4)+"\n")
   file.write(str(line5))
