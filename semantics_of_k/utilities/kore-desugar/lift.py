#!/usr/bin/python
import re
import os

p1 = re.compile("[a-zA-Z]\w*\'?:[a-zA-Z]\w*\'?$") #X:S
p2 = re.compile("\A\\\\[a][n][d]\(.+\)$") #phi1 /\ phi2
p3 = re.compile("\A\\\\[n][o][t]\(.+\)$") #not(phi)
p4 = re.compile("\A\\\\[e][x][i][s][t][s]\(.+\)$") #exists x:s,phi
p5 = re.compile("\A\\\\[e][q][u][a][l][s]\(.+\)$") #equals phi1, phi2, sort1, sort2
p6 = re.compile("\A\\\\[o][r]\(.+\)$") #phi1 \/ phi2
p7 = re.compile("[a-zA-Z]\w*\'?::[a-zA-Z]\w*\'?$") #meta-level pattern
p8 = re.compile("\A\\\\?[a-zA-Z]+(.+)$") #app(phi1,pih2,...,phin)
FIRST = False
ERROR = False
#pattern = str(raw_input("Enter a pattern :"))

nilPs = "#nilPattern"
appendPs = "#appendPatternList"
nilSs = "#nilSort"
appendSs = "#appendSortList"

def getArgSort(str):
	#print str
	if str.count("(") < str.count(")") :
		str = str[0:len(str)-1]
	if p1.match(str) :
		res = (re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?)",str).group(2))
	elif p2.match(str):
		tmp = str[5:len(str)-1] 
		pos = tmp.index(",")
		while 1 :
			if tmp[0:pos].count('(') == tmp[0:pos].count(')'):
				res =  getArgSort(tmp[0:pos])
				break
			else: 
				pos = pos + tmp[pos+1:len(tmp)].index(",") + 1
	elif p3.match(str):
		res = getArgSort(str[5:len(str)-1])
	elif p4.match(str):
		res = getArgSort((re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?),(.+)", \
			str[8:len(str)-1]).group(3)))
	elif p5.match(str):
		tmp = str[5:len(str)-1] 
		while 1 :
			if tmp[0:pos].count('(') == tmp[0:pos].count(')'):
				res = getArgSort(tmp[0:pos])
			else: 
				pos = pos + tmp[pos+1:len(tmp)].index(",") + 1
	elif p6.match(str):
		tmp = str[4:len(str)-1] 
		pos = tmp.index(",")
		while 1 :
			if tmp[0:pos].count('(') == tmp[0:pos].count(')'):
				res =  getArgSort(tmp[0:pos])
				break
			else: 
				pos = pos + tmp[pos+1:len(tmp)].index(",") + 1
	elif p7.match(str):
		res = (re.search("([a-zA-Z]*)::([a-zA-Z]*)",str).group(2))
	elif p8.match(str):
		pos_paren = str.index("(")
		key = str[0:pos_paren]
		res = dict_return[key]
	else : res = str
	#print "res" + res
	return res

comment = """def getResSort(str):
	res = ""
	#res += str.replace("*",)
	ls = dict_return.values()
	ls = list(set(ls))
	#print ls
	lens = len(ls) -1
	while lens >= 0 :
		res += str.replace("*",ls[lens]) + "\n"
		lens = lens -1
	return res"""

def lift(str):
	global FIRST 
	global ERROR
	if p1.match(str) :
		FIRST = False
		return "#variable(\"" + \
    	       (re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?)",str).group(1)) + \
               "\",#sort(\"" + \
               (re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?)",str).group(2)) + \
                "\"))"
	elif p2.match(str):
		if FIRST :
			tmp = str[5:len(str)-2] 
		else :
			tmp = str[5:len(str)-1] 
		#print FIRST
		FIRST = False
		pos = tmp.index(",")
		while 1 :
			if tmp[0:pos].count('(') == tmp[0:pos].count(')'):
				if getArgSort(tmp[0:pos]) != getArgSort(tmp[pos+1:len(tmp)]):
					print "not well formed in " + str
				return "#and(" + \
				   	lift(tmp[0:pos]) + \
				   	"," + \
				   	lift(tmp[pos+1:len(tmp)]) + \
				   	")"
			else: 
				pos = pos + tmp[pos+1:len(tmp)].index(",") + 1
	elif p3.match(str):
		if FIRST :
			FIRST = False
			return "#not(" + \
			   	lift(str[5:len(str)-2]) + ")"
		else :
			FIRST = False
			return "#not(" + \
			   	lift(str[5:len(str)-1]) + ")"
	elif p4.match(str):
		if FIRST : 
			tmp = str[8:len(str)-2]
		else : 
			tmp = str[8:len(str)-1]
		FIRST = False
		return "#exists(\"" + \
			   (re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?),(.+)",tmp).group(1)) + \
               "\",#sort(\"" + \
               (re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?),(.+)",tmp).group(2)) + \
			   "\")," + \
			   lift((re.search("([a-zA-Z]\w*\'?):([a-zA-Z]\w*\'?),(.+)",tmp).group(3))) + \
			   ")"
	elif p5.match(str):
		if FIRST : 
			tmp = str[8:len(str)-2]
		else : 
			tmp = str[8:len(str)-1]
		FIRST = False
		pos = tmp.index(",")
		while 1 :
			if tmp[0:pos].count('(') == tmp[0:pos].count(')'):
				if getArgSort(tmp[0:pos]) != getArgSort(tmp[pos+1:len(tmp)]):
					print "not well formed in " + str
				if getArgSort(tmp[0:pos]).count("#") ==0 :
					s1 = "\\forall(s:#Sort," + \
						"#equals(" + \
				   		lift(tmp[0:pos]) + \
				   		"," + \
				   		lift(tmp[pos+1:len(tmp)]) + ",#sort(\"" + \
				   		getArgSort(tmp[0:pos]) + "\"),s:#Sort))"
				else :
					s1 = "\\forall(s:#Sort," + \
						"#equals(" + \
				   		lift(tmp[0:pos]) + \
				   		"," + \
				   		lift(tmp[pos+1:len(tmp)]) + "," + \
				   		getArgSort(tmp[0:pos]) + ",s:#Sort))" 
				return s1
			else: 
				pos = pos + tmp[pos+1:len(tmp)].index(",") + 1
	elif p6.match(str):
		if FIRST :
			tmp = str[4:len(str)-2] 
		else :
			tmp = str[4:len(str)-1] 
		#print FIRST
		FIRST = False
		pos = tmp.index(",")
		while 1 :
			if tmp[0:pos].count('(') == tmp[0:pos].count(')'):
				if getArgSort(tmp[0:pos]) != getArgSort(tmp[pos+1:len(tmp)]):
					print "not well formed in " + str
				return "#or(" + \
				   	lift(tmp[0:pos]) + \
				   	"," + \
				   	lift(tmp[pos+1:len(tmp)]) + \
				   	")"
			else: 
				pos = pos + tmp[pos+1:len(tmp)].index(",") + 1
	elif p7.match(str):
		x = (re.search("([a-zA-Z]\w*\'?)::([a-zA-Z]\w*\'?)",str).group(1))
		s = (re.search("([a-zA-Z]\w*\'?)::([a-zA-Z]\w*\'?)",str).group(2))
		if s.count("#") == 0 :
			s1 = "#and(" + x + ":#Pattern," + \
					"\\forall(s:#Sort,#equals(#sort(\"" + s + "\")," + \
					"#getSort(#Pattern),#sort(\"" + s + "\"),s:#Sort)))"
		else :
			s1 = "#and(" + x + ":#Pattern," + \
					"\\forall(s:#Sort,#equals(#sort(\"" + s + "\")," + \
					"#getSort(#Pattern)," + s + ",s:#Sort)))"
		return s1
	elif p8.match(str):
		#print str
		if str.count("(") == 0 :
			return "[not pattern]: " + str
		pos_paren = str.index("(")
		key = str[0:pos_paren]
		if FIRST :
			tmp = str[pos_paren+1:len(str)-2]
		else :
			tmp = str[pos_paren+1:len(str)-1]
		FIRST = False
		liftList = ""
		if tmp.count("#") > 0 : #assume write true
			return "#application(#symbol(\"" + str[0:pos_paren] + \
				   "\"," + dict_arg[key] + "," + \
				    dict_return[key] + ")," + tmp + ")"
		if tmp.count(",") == 0 :
			#print lift(str[pos_paren+1:len(str)-1])
			if getArgSort(tmp) != "" and getArgSort(tmp) not in dict_arg[key] :
				print "sort not match in " + key
			#print  getArgSort(tmp) + "<> " + dict_arg[key]
			return "#application(#symbol(\"" + str[0:pos_paren] + \
				   "\"," + dict_arg[key] + ",#sort(\"" + \
				    dict_return[key] + "\"))," + lift(tmp) + ")"
		else :
			pos = tmp.index(",")
			i = 0
			num_pattern = 0
			args = dict_arg[key]
			args_ls = args.split(",")
			while pos < len(tmp) - 1 :
				if tmp[i:pos].count('(') == tmp[i:pos].count(')'):
					if getArgSort(tmp[i:pos]) != "" and getArgSort(tmp[i:pos]) not in args_ls[num_pattern] :
						print "sort not match in " + key
					num_pattern = num_pattern +1
					liftList += "." + lift(tmp[i:pos]) 
					i = pos + 1
				if pos + 1 >= len(tmp) :
					break
				if tmp[pos+1:len(tmp)].count(",") == 0 : 
					if getArgSort(tmp[i:len(tmp)]) != "" and \
					getArgSort(tmp[i:len(tmp)]) not in args_ls[len(args_ls)-1] :
						print "sort not match in " + key
					liftList += "." + lift(tmp[i:len(tmp)])
					break 
				pos = pos + tmp[i:len(tmp)].index(",") + 1
			if liftList != nilPs  and liftList.count(".") > 0 :
				count_paren = liftList.count(".") - 1
				liftList = liftList.replace(".", ","+appendPs + "(", count_paren)
				while count_paren > 0 :
					liftList = liftList + ")"
					count_paren = count_paren -1
				liftList = liftList[1:len(liftList)]
				liftList = liftList.replace(".",",")
			ls = liftList.split('\n')
			lens = len(ls) -1
			res = ""
			return "#application(#symbol(\"" + str[0:pos_paren] + \
					"\"," + dict_arg[key] + ", #sort(\"" + dict_return[key]+"\"))," + \
					liftList + ")"
 	else :
 		str = str.replace("\n","").replace("\t","")
 		if len(str) == 0 :
 			return nilPs
		else : 
			return "[not pattern]: " + str

dict_arg = {}
dict_return = {}
dict_module = {}
list_meta = []
result = ""
#record syntax part 
file_object = open('input.kore.txt')
file_mid = open('mid.kore.txt','w')
for line in file_object:
	if line.count("module") > 0 and line.count("endmodule") == 0 :
		name = (re.search("module ([a-zA-Z]\w*)",line).group(1))
		dict_module[name] = ""
		file_mid.write(line)
	elif line.count("import") > 0 :
		import_name = (re.search(" *import ([a-zA-Z]\w*)",line).group(1))
		file_mid.write(dict_module[import_name])
	elif line.count("syntax") > 0 :
		lineList = []
		file_mid.write(line)
		dict_module[name] += line.replace("	","") + "\n\n"
		if line.count("::=") == 0 : continue 
		line = line.replace("syntax ","")
		line = line.replace(" ","")
		line = line.replace("	","")
		#print line
		line_right = (re.search("(.*)::=(.*)", line).group(2))
		lineList = line_right.split('|')
		#print lineList
		num = len(lineList) -1
		while num >= 0 :
			group = lineList[num]
			key = (re.search("([a-zA-Z]\w*\'?)(\(?.*\)?)",group).group(1))
			value = (re.search("([a-zA-Z]\w*\'?)(\(?.*\)?)",group).group(2))
			value_return = (re.search("(.*)::=([a-zA-Z]\w*\'?\(?.*\)?)", \
			    	line).group(1))
			dict_return[key] = value_return 
			if value.count("#") > 0 :
				dict_arg[key] = value.replace("(","").replace(")","")
			else :
				value = value.replace("(","\"").replace(")","\"")
				value = value.replace(" ","").replace(",","\",\"").replace(",\"","),#sort(\"")
				value = "#sort(" + value + ")"
				if value == "#sort()" : value = nilSs
				else :
					count_paren = value.count(",")
					value = "," + value
					value = value.replace(",", ","+ appendSs+"(", count_paren)
					while count_paren > 0 :
						value = value + ")"
						count_paren = count_paren -1
					value = value[1:len(value)]
			#value_return = (re.search("(.*)::=([a-zA-Z]\w*\'?\(?.*\)?)", \
			#    	line).group(1))
				dict_arg[key] = value
			#print key + " " + dict_arg[key] + " " + dict_return[key]
			#dict_return[key] = value_return 
			num = num -1
	elif line.count("axiom") > 0 :
		file_mid.write(line)
		dict_module[name] += line.replace("	","") + "\n\n"
	elif line.count("endmodule") > 0 :
		file_mid.write(line) #dictionary need to be cleared here
file_mid.close()
file_object.close( )
##print dict_arg.keys()
comment = """#easy error matching check
file_object = open('input.kore.txt')
for line in file_object:
	if line.count("::=") == 0 or line.count("|") > 0 or line.count("#") :
		continue
	line = (re.search("(.*)::=(.*)", line).group(2))
	if line.count("(") > 0 :
		pos_paren = line.index("(")
		name = line[0:pos_paren]
		sorts = line[pos_paren+1:len(line)-1]
		#print name + " " + sorts
		sortList = sorts.split(",")
		#print sortList
		lens = len(sortList) - 1
		while lens >=0 :
			if sortList[lens] not in dict_arg[name.replace(" ","")] :
				ERROR = True
				break
			lens = lens -1
file_object.close( )"""
# lift part
file_object = open('mid.kore.txt')
name = ""
for line in file_object:
	FIRST = True
	if line.count("module") > 0 and line.count("endmodule") == 0 :
		result += line + "\n"
		name = (re.search("module ([a-zA-Z]\w*)",line).group(1))
		dict_module[name] = ""
	elif line.count("endmodule") > 0 :
		result += line + "\n"
	#elif line.count("import") > 0 :
	#	import_name = (re.search(" *import ([a-zA-Z]\w*)",line).group(1))
	#	result += dict_module[import_name]
	elif line.count("syntax") > 0 and line.count("#") > 0 :
		result += line.replace("	","") + "\n"
		meta_name = (re.search("(.*)::= ?([a-zA-Z]+)\(.*\)", line).group(2))
		list_meta.append(meta_name)
		dict_module[name] += line.replace("	","") + "\n\n"
	elif line.count("axiom") > 0 :
		line = line.replace("axiom ","")
		line = line.replace(" ","")
		line = line.replace("	","")
		#print line
		#print lift(line) 
		result += "axiom " + lift(line) +"\n\n"
		#print dict_module.keys()
		dict_module[name] += "axiom " + lift(line) +"\n\n"
file_object.close( )
if ERROR :
	print "error of sort matching detected. No output file available."
else :
	file_object = open('output.kore.txt','w')
	file_object.write(result)
	file_object.close( )
os.remove('mid.kore.txt')

	
