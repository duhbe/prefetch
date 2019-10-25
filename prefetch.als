// ====================================================
//	Alloy specification of the prefetch mechanism
//	E. Jenn - 2019/10/24
// Nota: I have used different names for the same "field" (e.g., pspr_c and pspr_u)
// in order to facilitate the parsing of the XML file. 
// Otherwise, X in sig1 and X in sig2 will designate a relation X with elements from sig1 or sig2
// which wil have to be sorted out during parsing.
// I have not used singletons to designate "fixed elements" such as cores, psprs,...
// but constraints on the cardinality. 
// ====================================================

module prefetch

open util/integer as myint

// ====================================================
// Flash memory banks
// ====================================================
abstract sig MemBanks {}

// ====================================================
// PSPRs
// ====================================================
abstract sig PSPRs {}

// ====================================================
// Cores
// ====================================================
abstract sig Cores {
	// Each core has a schedule...
	sched_c : one Schedules,
	// and a PSPR
	pspr_c : one PSPRs
}

// All cores
one sig Core0, Core1, Core2 extends Cores {}

// ====================================================
// Schedules
// ====================================================
sig Schedules {
	// Each schedule has some operations... 
	ops : some Ops
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
// Operations
// ====================================================
abstract sig Ops {
	// An operation starts its execution at a given time.
	start : one Int,
}
{
	// To make models easier to read
	start >= 0
}

// ====================================================
// Virtual operations (take no time to execute)
// ====================================================
abstract sig VirtualOps extends Ops {}

// ====================================================
// Actual operations (take time to execute)
// ====================================================
abstract sig ActualOps extends Ops {
	// The duration of execution of an operation
	duration :  Int
}
{
	// A duration can't be null.
	duration > 0
}

// ====================================================
// Functional operations (Fops)
// ====================================================
sig Fops extends ActualOps {
	// Each functional operation has a deadline
	deadline : Int,
	// ... zero or several predecessors
	preds : set Fops,
	// ... and requires a set of code blocks to execute
	cbs : some CodeBlocks
}
{
	// A functional op cannot be its own predecessor 
	this not in preds  
	// ... and cannot require more code blocks that what can be stored in the PSPR (here: 4 blocks)
	#cbs < 4 
}

// ====================================================
// Load operations (Lops)
// ====================================================
sig Lops extends ActualOps {
	// The code block to be loaded...
	cb : one CodeBlocks,
	// ... the PSPR to which the code block must be loaded
	pspr_l: one PSPRs
}
{
	// The time to load a block is arbitrarily set to 1 unit of time
	duration = 1
}

// ====================================================
// Unloading operations (Uops)
// ====================================================
sig Uops extends VirtualOps {
	// The code block to be unloaded
	cb : one CodeBlocks,
	// ... PSPR to which the code block must be "unloaded"
	pspr_u: one PSPRs
}

// ---------------------------------------------------------------------------------
// Any core has its own PSPR
// ---------------------------------------------------------------------------------
fact {
	all disj c,c': Cores | 
		c.pspr_c != c'.pspr_c
}

// ---------------------------------------------------------------------------------
// Any core has is own schedule
// ---------------------------------------------------------------------------------
fact {
	all disj c,c' : Cores | 
		c.sched_c != c'.sched_c
}	

// ---------------------------------------------------------------------------------
// Any PSPR belongs to a core (no dangling PSPRs)
// ---------------------------------------------------------------------------------
fact {
	all p : PSPRs | 
		one c : Cores |
			c.pspr_c = p
}

// ---------------------------------------------------------------------------------
// Any schedule belongs to one core
// ---------------------------------------------------------------------------------
fact {
	all s: Schedules  |
		one c : Cores | 
			c.sched_c = s
}	

// ---------------------------------------------------------------------------------
// Any op belongs to one and only one schedule 
// ---------------------------------------------------------------------------------
fact {
	all op: Ops  | 
		one s: Schedules |
			op in s.ops 
}


// ---------------------------------------------------------------------------------
// Any functional op shall terminate before its deadline
// ---------------------------------------------------------------------------------
fact CompleteBeforeDeadline{
	all op : Fops | 
		myint/plus[op.start,op.duration] <= op.deadline
}

// ---------------------------------------------------------------------------------
// There shall be no dependancy cycle between functional ops
// ---------------------------------------------------------------------------------
fact no_cycle {
	no op: Fops | 
		op in op.^preds
}

// ---------------------------------------------------------------------------------
// This predicate is true if the two ops do not temporarilly collide (on any schedule)
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
		( op in s.ops and op' in s.ops ) implies no_collision[op,op']
}

// ---------------------------------------------------------------------------------
// Loading ops shall not collide if they access to the same memory segment, even if 
// they are executed on different cores (so, on different schedules).
// ---------------------------------------------------------------------------------
fact NoCollisionBetweenBP {
	all s,s': Schedules, disj op,op' : Lops | 
		(op in s.ops and op' in s'.ops and op.cb.ms = op'.cb.ms) implies no_collision[op,op']
}

// ---------------------------------------------------------------------------------
// Functional operations shall be executed according to the "predessor" relation.
// ---------------------------------------------------------------------------------
fact {
	all op, op' : Fops | 
		op' in op.preds implies op'.start < myint/plus[op.start,op.duration]
}

// ---------------------------------------------------------------------------------
// Any code block must be used by at least one functional Op... (no "dangling" code block)
// ---------------------------------------------------------------------------------
fact {
	all cb :CodeBlocks | 
		cb in Fops.cbs
}

// ---------------------------------------------------------------------------------
// Any block shall only be loaded if it is used later.
// ---------------------------------------------------------------------------------
fact {
	all lop : Lops |
		some fop : Fops |
			( myint/plus[lop.start,lop.duration] <= fop.start ) and
			lop.cb in fop.cbs and
			one c: Cores | 
				fop in c.sched_c.ops  and lop.pspr_l = c.pspr_c
}

// ---------------------------------------------------------------------------------
// Any functional operation must have all its block available before starting execution.
// ---------------------------------------------------------------------------------
fact  {
	all fop: Fops |
		one c: Cores | fop in c.sched_c.ops and
		let loaded_blocks = { lop: Lops | 
			( lop.pspr_l = c.pspr_c ) and ( myint/plus[lop.start, lop.duration] <= fop.start ) }.cb |
		let unloaded_blocks = { uop: Uops | 
			( uop.pspr_u = c.pspr_c ) and ( uop.start <= fop.start ) }.cb  |
		fop.cbs in loaded_blocks-unloaded_blocks  
}

// ---------------------------------------------------------------------------------
// At any time, there shall be no more than N (here, N=3) code blocks in the buffer, i.e.: 
// At any time t, the number of loaded blocks minus the number of unloaded blocks before that point shall be 
// smaller or equal than N.
// We only consider significant times, i.e., times at which a load operaton is executed.
// ---------------------------------------------------------------------------------
fact {
	all p : PSPRs, lop: Lops |
		// at any time (time is defined by Load operations because an overflow can only be caused by a Load op)
		let loaded_blocks = { lop': Lops | 
				( lop'.pspr_l = p ) and ( myint/plus[lop'.start, lop'.duration] <= lop.start ) }.cb	|
		let unloaded_blocks = { uop: Uops | 
				( uop.pspr_u = p ) and ( uop.start <= lop.start ) }.cb |
		#loaded_blocks - #unloaded_blocks <= 3
 }


// ---------------------------------------------------------------------------------
// A code block cannot be unloaded if it has not been loaded before (in the same pspr)
// So, a Uops for code block <n> shall be preceeded by a Lops for code block <n>, with no
// other Uops' between the Lops and the Uops
// ---------------------------------------------------------------------------------
fact {
	all uop: Uops |
		some lop : Lops | 
			(myint/plus[lop.start, lop.duration] <= uop.start) and 
			( uop.cb = lop.cb ) and
			( uop.pspr_u = lop.pspr_l) and
			no uop': Uops | 
				( uop' != uop ) and 
				( myint/plus[lop.start, lop.duration] <= uop'.start) and 
				(uop'.start <= uop.start) and 
				( uop'.cb = uop.cb ) and
				( uop'.pspr_u = uop.pspr_u )
}


// ---------------------------------------------------------------------------------
// The same code block shall not be loaded twice in the same PSPR without being unloaded before:
// "Any sequence of operation containing two load op to the same PSPR must contain at least one unload op for the 
// same code block" (and the same pspr)
// ---------------------------------------------------------------------------------
fact NoTwoLoadsWithoutUnload{
	all lop, lop': Lops |
		( lop.pspr_l = lop'.pspr_l ) and ( lop.cb = lop'.cb ) and ( lop.start<lop'.start ) implies 
			some uop : Uops | 
				( myint/plus[lop.start, lop.duration] <= uop.start and 
				   uop.start <= myint/plus[lop'.start, lop'.duration]  ) 
				and
				( uop.cb = lop.cb ) and 
				( uop.pspr_u = lop.pspr_l )  
}

// ---------------------------------------------------------------------------------
// Predicate used to generate models
// ---------------------------------------------------------------------------------
pred show (){
	// We have only 2 memory banks
	#MemBanks = 2
	// Generate models with a maximum number of functional operations  
	#Fops = 6
	// Aditional constraints to ensure that fops use different blocks
	// all disj op, op' : Fops |
	 //	disj [op.cbs,  op'.cbs]
	// We limit the durations of Fop to one
	all fop : Fops |
		fop.duration = 1

	all fop : Fops |
		fop.start < 10

}

// ---------------------------------------------------------------------------------
// By default, Alloy integers are 4-bit twos-complement values, so the range of possible values runs from -8 to 7.
// To support  cardinalities greater than 7, int must be extended (extended to 5 bits)
// "run show for <X> means that there shall be no more than 20 instance for each signature.
// ---------------------------------------------------------------------------------
run show for 10 but 6 int
