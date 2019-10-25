#-------------------------------------------------------
# Crappy Python script to display a prefetch model 
# computed using "prefetc.als" processed by Alloy.
# E. Jenn 2019/10/24
#-------------------------------------------------------
from tkinter import *

import xml.etree.ElementTree as ET
root = ET.parse('U:/Work/prefetch/sol1.xml').getroot()

# Create op to deadline dict
op_to_deadline = dict()

for type_tag in root.findall('.//field[@label=\'deadline\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    deadline = int(atoms[1].get('label'))
    op_to_deadline[op]= deadline

print("Deadlines: ",end='')
print(op_to_deadline)

# Create op to start time dict
op_to_start = dict()

for type_tag in root.findall('.//field[@label=\'start\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    start = int(atoms[1].get('label'))
    op_to_start[op]= start

print("Start: ",end='')
print(op_to_start)

# Create op to schedule dict
op_to_schedule = dict()

for type_tag in root.findall('.//field[@label=\'ops\']/tuple'):
    atoms = type_tag.findall('atom')
    schedule = int(atoms[0].get('label').split('$')[1])
    op = atoms[1].get('label')
    op_to_schedule[op] = schedule

print("Schedule: ",end='')
print(op_to_schedule)

# Create op to duration dict
op_to_duration = dict()

for type_tag in root.findall('.//field[@label=\'duration\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    duration = int(atoms[1].get('label'))
    op_to_duration[op] = duration

print("Duration: ",end='')
print(op_to_duration)

# Create luop to mem blocks dict
luop_to_blocks = dict()

for type_tag in root.findall('.//field[@label=\'cb\']/tuple'):
    atoms = type_tag.findall('atom')
    op = atoms[0].get('label')
    blk = int(atoms[1].get('label').split('$')[1])
    luop_to_blocks[op] = blk

print("Load/Unload blocks: ",end='')
print(luop_to_blocks)


# Create fop to memblocks dict
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

# Create memblocks to bank dict
blocks_to_bank = dict()

for type_tag in root.findall('.//field[@label=\'ms\']/tuple'):
    atoms = type_tag.findall('atom')
    blk = atoms[0].get('label')
    bank = int(atoms[1].get('label').split('$')[1])
    blocks_to_bank[blk] = bank

print("Banks: ",end='')
print(blocks_to_bank)

# Create lop to pspr dict
lop_to_pspr = dict()

for type_tag in root.findall('.//field[@label=\'pspr_l\']/tuple'):
    atoms = type_tag.findall('atom')
    lop = atoms[0].get('label')
    pspr = int(atoms[1].get('label').split('$')[1])
    lop_to_pspr[lop] = pspr

print("Lop to PSPR: ",end='')
print(lop_to_pspr)

# Create core to PSPR dict
core_to_pspr = dict()

for type_tag in root.findall('.//field[@label=\'pspr_c\']/tuple'):
    atoms = type_tag.findall('atom')
    core = atoms[0].get('label')
    pspr = int(atoms[1].get('label').split('$')[1])
    core_to_pspr[core] = pspr

print("Core to PSPR: ",end='')
print(core_to_pspr)

# Create sched to core dict
sched_to_core = dict()

for type_tag in root.findall('.//field[@label=\'sched_c\']/tuple'):
    atoms = type_tag.findall('atom')
    core = atoms[0].get('label')
    sched = int(atoms[1].get('label').split('$')[1])
    sched_to_core[sched] = core

print("Sched to core: ",end='')
print(sched_to_core)

# Create core to PSPR dict
core_to_pspr = dict()

for type_tag in root.findall('.//field[@label=\'pspr_c\']/tuple'):
    atoms = type_tag.findall('atom')
    core = atoms[0].get('label')
    pspr = int(atoms[1].get('label').split('$')[1])
    core_to_pspr[core] = pspr

print("Core to PSPRs: ",end='')
print(core_to_pspr)

# Create op to PSPR dict
op_to_pspr = dict()
for op in op_to_start:
    op_to_pspr[op] = core_to_pspr[sched_to_core[op_to_schedule[op]]]

print("Op to PSPR: ",end='')
print(op_to_pspr)


# Size of a graphical slot
k_ssx = 80 # x axis
k_ssy = 20 # y axis

# Vertical separation between slots
k_vsy = 50

# Display graphical representation
max_start = -1
for op in op_to_start :
    if op_to_start[op] > max_start:
        max_start = op_to_start[op] 
        max_op = op
if max_op[0] == 'U':
    scrollregion_max_x = max_start*k_ssx+2*k_ssx
else:
    scrollregion_max_x = (max_start+op_to_duration[max_op])*k_ssx+2*k_ssx

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

nbcores = len(core_to_pspr)

# Draw the slots and number them
# (For those that are shocked by the non-factorized expressions, this is done on purpose. Thanks)
for i in range(0,40):
    canvas.create_text(100+i*k_ssx,70,fill="black",font="Arial 8",anchor='center', text=str(i))            
    for offy in range(0,nbcores):
        canvas.create_rectangle(100+i*k_ssx,100+offy*k_vsy,100+i*k_ssx+k_ssx,100+k_ssy+offy*k_vsy)      

# Draw the name of the PSPR
dy = 0
print(core_to_pspr.values())
for i in range(0,nbcores):
    canvas.create_text(80,100+dy+k_ssy/2,fill="black",font="Arial 8",anchor='e', text='PSPR #'+str(i))            
    dy += k_vsy

# Draw a legend
canvas.create_text(80,105+dy,fill="blue",font="Arial 10",anchor='w', text='Load operation : <op id>(<block #>)/<pspr #>)')            
dy += k_vsy/2
canvas.create_text(80,105+dy,fill="blue",font="Arial 10",anchor='w', text='Functional operation : <op id>([<block #>, <block #>,...]')            

# Draw the schedule
for op in op_to_start:
    # The type of the operation is determined by its first character (F, O, L)
    optype = op[0]
    color = optype_to_color[optype]
    # Compute the x and y offsets
    offx = op_to_start[op]*k_ssx
    offy = op_to_pspr[op]*k_vsy
    # Process "Load" operations
    if optype == 'L':
        name=optype+op.split('$')[1]+'('+str(luop_to_blocks[op])+')'
        ex = op_to_duration[op]*k_ssx
        canvas.create_rectangle(100+offx,100+offy,100+offx+ex,100+offy+k_ssy, fill=color)
        canvas.create_text(100+offx+50,110+offy,fill="black",font="Arial 8",anchor='center', width=ex, text=name+'/'+str(lop_to_pspr[op]))        
    # Process "Functional" operations
    elif optype == 'F':
        name=op[0]+op.split('$')[1]+'('+str(fop_to_blocks[op])+')'
        ex = op_to_duration[op]*k_ssx
        canvas.create_rectangle(100+offx,100+offy,100+offx+ex,100+offy+k_ssy, fill=color)
        canvas.create_text(100+offx+k_ssx/2,100+offy+k_ssy/2,fill="black",font="Arial 8",anchor='center', width=ex, text=name)
    # Process "Unload" operations
    else:
        name=optype+op.split('$')[1]+'('+str(luop_to_blocks[op])+')'
        canvas.create_polygon(100+offx,100+offy,100+offx-5, 90+offy,k_ssx+offx+5, 90+offy, fill=color)
        canvas.create_text(100+offx,80+offy,fill="black",font="Arial 8",anchor='center', text=name)

mainWindow.mainloop()

