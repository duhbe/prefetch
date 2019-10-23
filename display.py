from tkinter import *

import xml.etree.ElementTree as ET
root = ET.parse('f:/Work/01 - Workspaces/workspace-alloy/sol1.xml').getroot()

op_to_deadline = dict()

for type_tag in root.findall('.//field[@label=\'deadline\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    deadline = int(atoms[1].get('label'))
    op_to_deadline[op]= deadline

print("Deadlines: ",end='')
print(op_to_deadline)

op_to_start = dict()

for type_tag in root.findall('.//field[@label=\'start\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    start = int(atoms[1].get('label'))
    op_to_start[op]= start

print("Start: ",end='')
print(op_to_start)


op_to_schedule = dict()

for type_tag in root.findall('.//field[@label=\'ops\']/tuple'):
    atoms = type_tag.findall('atom')
    schedule = int(atoms[0].get('label').split('$')[1])
    op = atoms[1].get('label')
    op_to_schedule[op] = schedule

print("Schedule: ",end='')
print(op_to_schedule)

op_to_duration = dict()

for type_tag in root.findall('.//field[@label=\'duration\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    duration = int(atoms[1].get('label'))
    op_to_duration[op] = duration

print("Duration: ",end='')
print(op_to_duration)

# Extract the list of code blocks for load/unload operations
luop_to_blocks = dict()

for type_tag in root.findall('.//field[@label=\'cb\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    blk = int(atoms[1].get('label').split('$')[1])
    luop_to_blocks[op] = blk

print("Load/Unload blocks: ",end='')
print(luop_to_blocks)


# Extract the list of code blocks for functional operations
fop_to_blocks = dict()

for type_tag in root.findall('.//field[@label=\'cbs\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    blk = int(atoms[1].get('label').split('$')[1])
    fop_to_blocks[op] = blk

print("Blocks for FOP: ",end='')
print(fop_to_blocks)

# 
blocks_to_bank = dict()

for type_tag in root.findall('.//field[@label=\'ms\']/tuple'):
    atoms = type_tag.findall('atom')
    blk = atoms[0].get('label')
    bank = int(atoms[1].get('label').split('$')[1])
    blocks_to_bank[blk] = bank

print("Banks: ",end='')
print(blocks_to_bank)




mainWindow = Tk()
mainWindow.title('Schedule')
mainWindow.geometry('1000x500+400+400')
frame=Frame(mainWindow, width=1000, height=500)
frame.grid(row=0,column=0)
canvas=Canvas(frame,bg='#FFFFFF',width=980, height=480, scrollregion=(0,0,1500,500))
hbar=Scrollbar(frame,orient=HORIZONTAL)
hbar.pack(side=BOTTOM,fill=X)
hbar.config(command=canvas.xview)
vbar=Scrollbar(frame,orient=VERTICAL)
vbar.pack(side=RIGHT,fill=Y)
vbar.config(command=canvas.yview)
canvas.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
canvas.pack(side=LEFT,expand=True,fill=BOTH)

optype_to_color = {'F': "lightblue", 'L': "pink", 'U': "lightgreen" }

for offy in range(0,10):
    for i in range(0,40):
        canvas.create_rectangle(100+i*50,100+offy*50,100+i*50+50,120+offy*50)

for op in op_to_start:
    print(op)
    
    optype = op[0]
    color = optype_to_color[optype]
    sx = op_to_start[op]*50

    offy = op_to_schedule[op]*50
    
    if optype == 'L':
        name=optype+op.split('$')[1]+'('+str(luop_to_blocks[op])+')'
        ex = op_to_duration[op]*50
        canvas.create_rectangle(100+sx,100+offy,100+sx+ex,120+offy, fill=color)
        canvas.create_text(100+sx+25,110+offy,fill="black",font="Arial 8",anchor='center', width=ex, text=name)        
    
    if optype == 'F':
        name=op[0]+op.split('$')[1]+'('+str(fop_to_blocks[op])+')'
        ex = op_to_duration[op]*50
        canvas.create_rectangle(100+sx,100+offy,100+sx+ex,120+offy, fill=color)
        canvas.create_text(100+sx+25,110+offy,fill="black",font="Arial 8",anchor='center', width=ex, text=name)
    
    if optype == 'U':
        name=optype+op.split('$')[1]+'('+str(luop_to_blocks[op])+')'
        canvas.create_polygon(100+sx,100+offy,100+sx-5, 90+offy,100+sx+5, 90+offy, fill=color)
        canvas.create_text(100+sx,80+offy,fill="black",font="Arial 8",anchor='center', width=ex, text=name)

mainWindow.mainloop()

