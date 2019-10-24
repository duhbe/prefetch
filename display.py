#-------------------------------------------------------
# Crappy Ptyhon script to display a solution computed by 
# Alloy.
# Eric 2019/10/24
#-------------------------------------------------------
from tkinter import *

import xml.etree.ElementTree as ET
root = ET.parse('U:/Work/prefetch/sol1.xml').getroot()

# Load Fop deadlines
op_to_deadline = dict()

for type_tag in root.findall('.//field[@label=\'deadline\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    deadline = int(atoms[1].get('label'))
    op_to_deadline[op]= deadline

print("Deadlines: ",end='')
print(op_to_deadline)

# Load start times
op_to_start = dict()

for type_tag in root.findall('.//field[@label=\'start\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    start = int(atoms[1].get('label'))
    op_to_start[op]= start

print("Start: ",end='')
print(op_to_start)

# Load schedules
op_to_schedule = dict()

for type_tag in root.findall('.//field[@label=\'ops\']/tuple'):
    atoms = type_tag.findall('atom')
    schedule = int(atoms[0].get('label').split('$')[1])
    op = atoms[1].get('label')
    op_to_schedule[op] = schedule

print("Schedule: ",end='')
print(op_to_schedule)

# Load durations
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
# [TODO: display all blocks: for the moment, we only display one block]
fop_to_blocks = dict()

for type_tag in root.findall('.//field[@label=\'cbs\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    blk = int(atoms[1].get('label').split('$')[1])
    if not ( op in fop_to_blocks.keys() ) :
        fop_to_blocks[op] = []
    fop_to_blocks[op].append(blk)

print("Blocks for FOP: ",end='')
print(fop_to_blocks)

# Load banks
blocks_to_bank = dict()

for type_tag in root.findall('.//field[@label=\'ms\']/tuple'):
    atoms = type_tag.findall('atom')
    blk = atoms[0].get('label')
    bank = int(atoms[1].get('label').split('$')[1])
    blocks_to_bank[blk] = bank

print("Banks: ",end='')
print(blocks_to_bank)

# Load pspr
core_lop_to_pspr = dict()

for type_tag in root.findall('.//field[@label=\'pspr\']/tuple'):
    atoms = type_tag.findall('atom')
    blk = atoms[0].get('label')
    bank = int(atoms[1].get('label').split('$')[1])
    core_lop_to_pspr[blk] = bank

print("PSPR: ",end='')
print(core_lop_to_pspr)

# Load schedules
core_to_sched = dict()

for type_tag in root.findall('.//field[@label=\'sched\']/tuple'):
    atoms = type_tag.findall('atom')
    blk = atoms[0].get('label')
    bank = int(atoms[1].get('label').split('$')[1])
    core_to_sched[blk] = bank

print("Core to Scheds: ",end='')
print(core_to_sched)

# Size of a graphical slot
k_ss = 100

# Display graphical representation
max_start = -1
for i in op_to_start :
    if op_to_start[i] > max_start:
        max_start = op_to_start[i] 
        max_i = i
scrollregion_max_x = (max_start+op_to_duration[max_i])*k_ss+k_ss

mainWindow = Tk()
mainWindow.title('Schedule')
mainWindow.geometry('1000x500+400+400')
frame=Frame(mainWindow, width=1000, height=500)
frame.grid(row=0,column=0)
canvas=Canvas(frame,bg='#FFFFFF',width=980, height=480, scrollregion=(0,0,scrollregion_max_x,500))
hbar=Scrollbar(frame,orient=HORIZONTAL)
hbar.pack(side=BOTTOM,fill=X)
hbar.config(command=canvas.xview)
vbar=Scrollbar(frame,orient=VERTICAL)
vbar.pack(side=RIGHT,fill=Y)
vbar.config(command=canvas.yview)
canvas.config(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
canvas.pack(side=LEFT,expand=True,fill=BOTH)

optype_to_color = {'F': "lightblue", 'L': "pink", 'U': "lightgreen" }

# Draw the slots and number them
# (For those that are shocked by the non-factorized expressions, this is done on purpose. Thanks)
for i in range(0,40):
    canvas.create_text(k_ss+i*k_ss,70,fill="black",font="Arial 8",anchor='center', text=str(i))            
    for offy in range(0,10):
        canvas.create_rectangle(k_ss+i*k_ss,100+offy*50,k_ss+i*k_ss+k_ss,120+offy*50)      

for op in op_to_start:
    optype = op[0]
    color = optype_to_color[optype]
    sx = op_to_start[op]*k_ss

    offy = op_to_schedule[op]*k_ss
    
    if optype == 'L':
        name=optype+op.split('$')[1]+'('+str(luop_to_blocks[op])+')'
        ex = op_to_duration[op]*k_ss
        canvas.create_rectangle(k_ss+sx,100+offy,k_ss+sx+ex,120+offy, fill=color)
        canvas.create_text(k_ss+sx+50,110+offy,fill="black",font="Arial 8",anchor='center', width=ex, text=name+'/'+str(core_lop_to_pspr[op]))        
    
    if optype == 'F':
        name=op[0]+op.split('$')[1]+'('+str(fop_to_blocks[op])+')'
        ex = op_to_duration[op]*k_ss
        canvas.create_rectangle(k_ss+sx,100+offy,k_ss+sx+ex,120+offy, fill=color)
        canvas.create_text(k_ss+sx+k_ss/2,110+offy,fill="black",font="Arial 8",anchor='center', width=ex, text=name)
    
    if optype == 'U':
        name=optype+op.split('$')[1]+'('+str(luop_to_blocks[op])+')'
        canvas.create_polygon(k_ss+sx,100+offy,k_ss+sx-5, 90+offy,k_ss+sx+5, 90+offy, fill=color)
        canvas.create_text(k_ss+sx,80+offy,fill="black",font="Arial 8",anchor='center', text=name)

mainWindow.mainloop()

