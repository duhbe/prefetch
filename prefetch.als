// ====================================================
//	Alloy specification of the prefetch mechanism
//	E. Jenn - 2019/10/24
// ====================================================

module prefetch

open util/integer as myint

// ====================================================
// Flash memory banks
// ====================================================
abstract sig MemBanks {}

// ====================================================
// The PSPRs
// ====================================================
abstract sig PSPRs {}

// ====================================================
// The cores
// ====================================================
abstract sig Cores {
	// Each core has a schedule
	sched : one Schedules,
	// PSPR
	pspr : one PSPRs
}

// All cores
one sig Core0, Core1, Core2 extends Cores {}

// ====================================================
// The schedules
// ====================================================
sig Schedules {
	// All operations of the schedule 
	ops : set Ops
}

// ====================================================
// The code block.
// All code blocks have the same size.
// ====================================================
sig CodeBlocks {
	// A block is located in a memory segment
	ms : one MemBanks
}

// ====================================================
// Abstract operations
// ====================================================
abstract sig Ops {
	// An Op belongs to one and only one schedule
	sched : one Schedules,
	// The start time for the execution of an operation
	start : one Int,
}
{
	// To make models easier to read
	start >= 0
}

// ====================================================
// A vitual op takes no time to execute
// ====================================================
abstract sig VirtualOps extends Ops {}

// ====================================================
// Actual ops (an op that takes some timle to execute)
// ====================================================
abstract sig ActualOps extends Ops {
	// The duration of execution of an operation
	duration : one Int
}
{
	duration > 0
}

// ====================================================
// Functional Ops
// ====================================================
sig Fops extends ActualOps {
	// Each functional operation has a deadline
	deadline : Int,
	// A functional op has one or several predecessors
	preds : set Fops,
	// A functional op requires a set of code blocks to execute
	cbs : set CodeBlocks
}
{
	// A functional op cannot be its own predecessor 
	this not in preds  
	// A functional op requires at least one code block to do something useful
	#cbs > 0
	// but it cannot require more code blocks that what can be stored in the PSPR
	#cbs < 4 
}

// ====================================================
// Loading Ops
// ====================================================
// [TODO] Replace cb, pspr by xfer : cb->pspr
sig Lops extends ActualOps {
	// The code block to be loaded
	cb : one CodeBlocks,
	// The PSPR to which the code block must be loaded
	pspr: one PSPRs
}
{
	// The time to load a blcok is arbitrarily set to 1
	duration = 1
}

// ====================================================
// Unloading operations
// ====================================================
sig Uops extends VirtualOps {
	// The code block to be unloaded
	cb : one CodeBlocks,
	// The PSPR to which the code block must be unloaded
	pspr: one PSPRs
}

// ---------------------------------------------------------------------------------
// Each core has its own PSPR
// ---------------------------------------------------------------------------------
fact {
	all disj c,c': Cores | 
		c.pspr != c'.pspr
}

// ---------------------------------------------------------------------------------
// Each PSPR belongs to a core
// ---------------------------------------------------------------------------------
fact {
	all p : PSPRs | 
		one c : Cores |
			c.pspr = p
}

// ---------------------------------------------------------------------------------
// Each core has is own schedule
// ---------------------------------------------------------------------------------
fact {
	all disj c,c' : Cores | 
		c.sched != c'.sched
}	

// ---------------------------------------------------------------------------------
// Each schedule belongs to one core
// ---------------------------------------------------------------------------------
fact {
	all s: Schedules  |
		one c : Cores | 
			c.sched = s
}	

// ---------------------------------------------------------------------------------
// Any functional op shall terminate before its deadline
// ---------------------------------------------------------------------------------
fact CompleteBeforeDeadline{
	all op : Fops | 
		myint/plus[op.start,op.duration]<= op.deadline
}

// ---------------------------------------------------------------------------------
// There shall be no dependancy cycle between functional ops
// ---------------------------------------------------------------------------------
fact no_cycle {
	no op: Fops | 
		op in op.^preds
}

// ---------------------------------------------------------------------------------
// This predicate is true if the two ops temporarilly collide (on any schedule)
// ---------------------------------------------------------------------------------
pred no_collision  [op: Ops, op': Ops]
{
	(myint/plus[op.start, op.duration] <= op'.start) or
	(myint/plus[op'.start, op'.duration] <= op.start)
}

// ---------------------------------------------------------------------------------
// Functional and loading ops in a schedule shall not collide.
// ---------------------------------------------------------------------------------
fact NoCollision {
	all s: Schedules, disj op,op' : Fops+Lops | 
		op in s.ops and op' in s.ops implies no_collision[op,op']
}

// ---------------------------------------------------------------------------------
// Loading ops shall not collide if they access to the same segment, even if 
// they are on different schedules.
// ---------------------------------------------------------------------------------
fact NoCollisionBetweenBP {
	all s,s': Schedules, disj op,op' : Lops | 
		(op in s.ops and op' in s'.ops and op.cb.ms = op'.cb.ms) implies no_collision[op,op']
}

// ---------------------------------------------------------------------------------
// The predecessors must be executed before the successors.
// ---------------------------------------------------------------------------------
fact {
	all op, op' : Fops | 
		op' in op.preds implies op'.start < myint/plus[op.start,op.duration]
}

// ---------------------------------------------------------------------------------
// Each op belongs to one and only one schedule 
// ---------------------------------------------------------------------------------
fact {
	all op: Ops  | 
		one s: Schedules |
			op in s.ops 
}

// ---------------------------------------------------------------------------------
// All code blocks must be used by at least one functional Op...
// ---------------------------------------------------------------------------------
fact {
	all cb :CodeBlocks | 
		cb in Fops.cbs
}

// ---------------------------------------------------------------------------------
// We shall only load a code block that is used later
// ---------------------------------------------------------------------------------
fact {
	all lop : Lops |
		some fop : Fops |
			( myint/plus[lop.start,lop.duration] <= fop.start ) and
			lop.cb in fop.cbs and
			one c: Cores | fop in c.sched.ops  and lop.pspr = c.pspr
}

// ---------------------------------------------------------------------------------
// No functional operation can start before its code blocks have been loaded.
// ---------------------------------------------------------------------------------
fact  {
	all fop: Fops |
		one c: Cores | fop in c.sched.ops and
		let loaded_blocks = { lop: Lops | 
				( lop.pspr = c.pspr ) and ( myint/plus[lop.start, lop.duration] <= fop.start ) }.cb |
		let unloaded_blocks = { uop: Uops | 
				( uop.pspr = c.pspr ) and ( uop.start <= fop.start ) }.cb  |
		fop.cbs in loaded_blocks-unloaded_blocks  
}

// ---------------------------------------------------------------------------------
// At any time, there shall be no more than N (here, N=3) code blocks in the buffer, i.e.: 
// At any time t, the number of loaded blocks minus the number of unloaded blocks before that point shall be 
// smaller or equal than N.
// We only consider significant times, i.e., times at which a Op is executed.
// ---------------------------------------------------------------------------------
fact {
	all p : PSPRs, lop: Lops |
		// at any time (time is defined by Load operations because an overflow can only be caused by a Load op)
		let loaded_blocks = { lop': Lops | 
				( lop'.pspr = p ) and ( myint/plus[lop'.start, lop'.duration] <= lop.start ) }.cb	|
		let unloaded_blocks = { uop: Uops | 
				( uop.pspr = p ) and ( uop.start <= lop.start ) }.cb |
		#loaded_blocks - #unloaded_blocks <= 2
 }


// ---------------------------------------------------------------------------------
// A code block cannot be unloaded if it has not been loaded before (in the same pspr)
// So, a Uops for code Op n shall be preceeded by a Lops for Op n, with no
// other Uops' between the Lops and the Uops
// ---------------------------------------------------------------------------------
fact {
	all uop: Uops |
		some lop : Lops | 
			(myint/plus[lop.start, lop.duration] <= uop.start) and 
			( uop.cb in lop.cb ) and
			( uop.pspr = lop.pspr) and
			no uop': Uops | 
				( uop' != uop ) and 
				( myint/plus[lop.start, lop.duration] <= uop'.start) and 
				(uop'.start <= uop.start) and 
				( uop'.cb = uop.cb ) and
				( uop'.pspr = uop.pspr )
}

// ---------------------------------------------------------------------------------
// There is no sense in loading a block if there is no functional op using
// this block late in the future.
// ---------------------------------------------------------------------------------
fact {
	all lop: Lops |
		some fop : Fops | 
			( myint/plus[lop.start, lop.duration] <= fop.start  )  and 
			( lop.cb in fop.cbs ) and 
			one c:Cores |
				( fop in c.sched.ops ) and  ( c.pspr = lop.pspr )
 }

// ---------------------------------------------------------------------------------
// The same code block shall not be loaded twice in the same PSPR without being unloaded before:
// "Any sequence of two successive load op to the same PSPR must contain at least one unload op for the 
// same code block" (and the same pspr)
// ---------------------------------------------------------------------------------
fact NoTwoLoadsWithoutUnload{
	all lop, lop': Lops |
		(lop.pspr = lop'.pspr) and (lop.cb = lop'.cb) and (lop.start<lop'.start) implies 
			some uop : Uops | 
				( myint/plus[lop.start, lop.duration] <= uop.start and 
				   uop.start <= myint/plus[lop'.start, lop'.duration]  ) 
				and
				uop.cb = lop.cb
}

// ---------------------------------------------------------------------------------
// Predicate used to generate models
// ---------------------------------------------------------------------------------
pred show (){
	// We have only 2 memory banks
	#MemBanks = 2
	// Generate models with a maximum number of functional operations  
	#Fops = 5
	// Aditional constraints to ensure that fops use different blocks
	all disj op, op' : Fops |
		disj [op.cbs,  op'.cbs]
}

// ---------------------------------------------------------------------------------
// By default, Alloy integers are 4-bit twos-complement values, so the range of possible values runs from -8 to 7.
// To support higher cardinality greater than 7, int must be extended (extended to 5 bits)
// ---------------------------------------------------------------------------------
run show for 10 but 6 int
