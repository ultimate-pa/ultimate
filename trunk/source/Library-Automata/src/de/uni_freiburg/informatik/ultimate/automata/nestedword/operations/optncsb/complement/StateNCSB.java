package complement;

import automata.IBuchi;

import automata.StateGeneral;

import main.Options;
import util.IntIterator;
import util.IntSet;
import util.PowerSet;
import util.UtilIntSet;

public class StateNCSB extends StateGeneral implements IStateComplement {


	private IntSet mNSet;
	private IntSet mCSet;
	private IntSet mSSet;
	private IntSet mBSet;
	
	private final IBuchi mOperand;
	private final BuchiComplementSDBA mComplement;
	
	public StateNCSB(int id, BuchiComplementSDBA complement) {
		super(id);
		// TODO Auto-generated constructor stub
		this.mComplement = complement;
		this.mOperand = complement.getOperand();
		this.mNSet = UtilIntSet.newIntSet();
		this.mCSet = UtilIntSet.newIntSet();
		this.mSSet = UtilIntSet.newIntSet();
		this.mBSet = UtilIntSet.newIntSet();
	}
	
	public void setSets(IntSet N, IntSet C, IntSet S, IntSet B) {
		this.mNSet =  N.clone();
		this.mCSet =  C.clone();
		this.mSSet =  S.clone();
		this.mBSet =  B.clone();
	}
	
	public IntSet getNSet() {
		return  mNSet.clone();
	}
	
	public IntSet getCSet() {
		return  mCSet.clone();
	}
	
	public IntSet getSSet() {
		return  mSSet.clone();
	}
	
	public IntSet getBSet() {
		return  mBSet.clone();
	}

	@Override
	public IBuchi getOperand() {
		return this.mOperand;
	}

	@Override
	public IBuchi getComplement() {
		return mComplement;
	}
	
	// support on-the-fly exploration
	private IntSet visitedLetters = UtilIntSet.newIntSet();
	
	
	@Override
	public IntSet getSuccessors(int letter) {
		if(visitedLetters.get(letter)) {
			return super.getSuccessors(letter);
		}
		if(Options.optNCSB) {
			return computeSuccessorsOptimized(letter);
		}else {
			return computeSuccessors(letter);
		}
	}
	

	public boolean equals(Object otherState) {
		if(!(otherState instanceof IStateComplement)) {
			return false;
		}
		StateNCSB state = (StateNCSB)otherState;
		return  contentEqual(state);
	}
	
	public boolean contentEqual(StateNCSB state) {
		if(! mNSet.equals(state.mNSet)
		|| ! mCSet.equals(state.mCSet)
		|| ! mSSet.equals(state.mSSet)
		|| ! mBSet.equals(state.mBSet)) {
			return false;
		}
		return true;
	}
	
	// check whether one state is covered by the other state (language-wise)
	// this.N >= other.N & this.C >= other.C & this.S >= other.S
	
	public boolean coveredBy(StateNCSB other) {

		if(! other.mNSet.subsetOf(mNSet)
		|| ! other.mCSet.subsetOf(mCSet)
		|| ! other.mSSet.subsetOf(mSSet)) {
			return false;
		}

		return true;
	}
	
	// this.N >= other.N & this.C >= other.C & this.S >= other.S & this.B >= other.B
	public boolean strictlyCoveredBy(StateNCSB other) {
		
		if(! other.mNSet.subsetOf(mNSet)
		|| ! other.mCSet.subsetOf(mCSet)
		|| ! other.mSSet.subsetOf(mSSet)
		|| ! other.mBSet.subsetOf(mBSet)) {
			return false;
		}

		return true;
	}
	
	
	public String toString() {
		return "(" + mNSet.toString() + "," + mCSet.toString() + ","
				+ mSSet.toString() + "," + mBSet.toString() + ")";
	}
	
	int hashCode;
	boolean hasCode = false;
	@Override
	public int hashCode() {
		if(hasCode) return hashCode;
		else {
			hasCode = true;
			hashCode = toString().hashCode();
		}
		return hashCode;
	}
	// -------------------------------------------------
	/**
	 * In order not to mess things up, use two different methods to
	 *   compute successors in different ways
	 *   */
	

	/**
	 *  implementation of NCSB complementation algorithm which is adapted from GOAL
	 */
	private IntSet computeSuccessors(int letter) {
//		Set<StateNCSB> succs = new HashSet<>();
		visitedLetters.set(letter);
		
		IntSet currNSet =  mNSet.clone();
		IntSet currCSet =  mCSet.clone();
		IntSet currSSet =  mSSet.clone();
		IntSet currBSet =  mBSet.clone();
		/*
		 * If q in C\F, then tr(q, a) is not empty
		 */
		IntSet F = mOperand.getFinalStates();
		IntSet cMinusF =  currCSet.clone();
		cMinusF.andNot(F); 
		IntIterator iter = cMinusF.iterator();
		while(iter.hasNext()) {
			if (mOperand.getSuccessors(iter.next(), letter).isEmpty()) {
				return UtilIntSet.newIntSet();
			}
		}
		// should have successors
		
		/* -------------- compute successors -----------------*/
		IntSet NSuccs = mOperand.getSuccessors(currNSet, letter);
		IntSet CSuccs = mOperand.getSuccessors(currCSet, letter);
		IntSet SSuccs = mOperand.getSuccessors(currSSet, letter);
		IntSet BSuccs = mOperand.getSuccessors(currBSet, letter);
		
		// record used transition (NOT necessary in complement)
		mComplement.useOpTransition(letter, currNSet);
		mComplement.useOpTransition(letter, currCSet);
		mComplement.useOpTransition(letter, currSSet);
		/* ------------------------------------------------*/
		
		// N successors
		IntSet Np =  NSuccs.clone();
				
		Np.andNot(F);            // remove final states
		Np.andNot(CSuccs);       // remove successors of C, the final states of NSuccs are in CSuccs 
		Np.andNot(SSuccs);       // remove successors of S
		
		// C successors
		IntSet Cp =  CSuccs.clone();
		IntSet nInterF =  NSuccs.clone();
		nInterF.and(F);
		Cp.or(nInterF);
		
		// S successors
		IntSet Sp =  SSuccs.clone();
		
		// B successors
		IntSet Bp =  BSuccs.clone();
		
		
		/* -------------- compute C' of C -----------------*/
		// firstly compute successors of C\F which must be in C'
		IntSet CMinusFSuccs = mOperand.getSuccessors(cMinusF, letter);
		
		// secondly compute successors of C/\ F which may have final states
		IntSet cInterF =  currCSet.clone(); 
		cInterF.and(F);  // get all accepting states in C
		IntSet CInterFSuccs = mOperand.getSuccessors(cInterF, letter);  // get successors of accepting states
		CInterFSuccs.andNot(F);                            // remove accepting state here
		CInterFSuccs.andNot(CMinusFSuccs);         // remove must-in C states
		
		// note that we should remove all final states which may go to S'

		/* ----------- make nondeterministic choices ------------------- */
		// the successors of C /\ F should go to C and S with nondeterministic choices
		
//		System.out.println(CInterFSuccs);
		PowerSet ps = new PowerSet(CInterFSuccs);
												
		while (ps.hasNext()) {
			IntSet Sextra = ps.next(); // extra states to be added into S'
			// if must-in states has overlap in Sextra
			if(Sextra.overlap(CMinusFSuccs)) continue;
			
			IntSet NPrime = Np;
			IntSet CPrime =  Cp.clone();
			CPrime.andNot(Sextra);
			IntSet SPrime =  Sp.clone();
			SPrime.or(Sextra);
			IntSet BPrime = null;
			if(currBSet.isEmpty()) {
				BPrime =  CPrime.clone();
			}else {
				BPrime =  Bp.clone();
				BPrime.andNot(Sextra);
			}

			if (! SPrime.overlap(F) && !CPrime.overlap(SPrime)) {
				StateNCSB succ = mComplement.addState(NPrime, CPrime, SPrime, BPrime);
				this.addSuccessor(letter, succ.getId());
//				succs.add(succ);
			}
		}

		return super.getSuccessors(letter);
	}
	

	
	/**
	 * The OPTIMIZED version, delay the word distribution 
	 * */
	private IntSet computeSuccessorsOptimized(int letter) {
		
		visitedLetters.set(letter);
		
		IntSet currNSet =  mNSet.clone();
		IntSet currCSet =  mCSet.clone();
		IntSet currSSet =  mSSet.clone();
		IntSet currBSet =  mBSet.clone();
		/*
		 * If q in B\F, then tr(q, a) is not empty
		 */
		IntSet F = mOperand.getFinalStates();
		IntSet bMinusF =  currBSet.clone();
		bMinusF.andNot(F); 
		IntIterator iter = bMinusF.iterator();
		while(iter.hasNext()) {
			if (mOperand.getSuccessors(iter.next(), letter).isEmpty()) {
				return UtilIntSet.newIntSet();
			}
		}
		// should have successors
		
		/* -------------- compute successors -----------------*/
		IntSet NSuccs = mOperand.getSuccessors(currNSet, letter);
		IntSet CSuccs = mOperand.getSuccessors(currCSet, letter);
		IntSet SSuccs = mOperand.getSuccessors(currSSet, letter);
		IntSet BSuccs = mOperand.getSuccessors(currBSet, letter);
		
		// record used transition (NOT necessary in complement)
		mComplement.useOpTransition(letter, currNSet);
		mComplement.useOpTransition(letter, currCSet);
		mComplement.useOpTransition(letter, currSSet);
		/* ------------------------------------------------*/
		
		boolean bIsEmpty = currBSet.isEmpty();
		// N successors
		IntSet Np =  NSuccs.clone();
				
		Np.andNot(F);            // remove final states
		Np.andNot(CSuccs);       // remove successors of C, the final states of NSuccs are in CSuccs 
		Np.andNot(SSuccs);       // remove successors of S
		
		// C successors, V'
		IntSet Cp =  CSuccs.clone();
		IntSet nInterF =  NSuccs.clone();
		nInterF.and(F);
		Cp.or(nInterF);
		
		// S successors
		IntSet Sp =  SSuccs.clone();
		
		// B successors
		IntSet Bp =  BSuccs.clone();
		
		
		/* -------------- compute word distribution to S' -----------------*/
		//  compute successors which can be added into S'
		IntSet mayIns = null;
		if(bIsEmpty) {
			// mustNots, must in C' d(N)/\F
			mayIns = CSuccs.clone();
			// may also delete states in CSuccs, I think we should move them to S
			// V'\(d(N)/\F), which may be in C'
			mayIns.andNot(nInterF); 
		}else {
			// set to empty
			IntSet bInterF = currBSet.clone();
			bInterF.and(F);
			// d(B/\F)  M'
			mayIns = mOperand.getSuccessors(bInterF, letter);
			// OPTIMIZATION, keep all d(B\F) successors
			IntSet bMinusFSuccs = mOperand.getSuccessors(bMinusF, letter);
			mayIns.andNot(bMinusFSuccs);
		}

//		System.out.println(CInterFSuccs);
		PowerSet ps = new PowerSet(mayIns);
												
		while (ps.hasNext()) {
			IntSet extra = ps.next(); // extra states to be added into S'
//			if(Sextra.overlap(mustNots)) continue;
			
			IntSet NPrime = Np;
			IntSet CPrime = null;
			IntSet SPrime = Sp.clone();
			IntSet BPrime = null;

			if(bIsEmpty) {
				// as usual S and C
				CPrime = nInterF.clone();
				CPrime.or(extra); // C' get extra
				BPrime = CSuccs.clone(); 
				BPrime.and(CPrime);     // B'= d(C) /\ C'
				IntSet temp = CSuccs.clone(); // V'
				temp.andNot(CPrime); // V'\C'
				SPrime.or(temp); // S'=d(S)\/(V'\C')
			}else {
				// B is not empty
				SPrime.or(extra); // d(S) \/ M'
				BPrime = Bp.clone();
				BPrime.andNot(extra); // B'=d(B)\M'
				CPrime = Cp.clone(); // V'
				CPrime.andNot(SPrime); // C'= V'\S'
			}

			// make sure S' /\ F and B' /\ S' are empty
			if (!SPrime.overlap(F) && !BPrime.overlap(SPrime)) {
				StateNCSB succ = mComplement.addState(NPrime, CPrime, SPrime, BPrime);
				this.addSuccessor(letter, succ.getId());
			}
		}

		return super.getSuccessors(letter);
	}	
	
	
	
	// not used any more -------------------------------------------
//	/**
//	 * The OPTIMIZED version, delay the word distribution 
//	 * */
//	private IntSet computeSuccessorsOptimized(int letter) {
//		
////		Set<StateNCSB> succs = new HashSet<>();
//		visitedLetters.set(letter);
//		
//		IntSet currNSet =  mNSet.clone();
//		IntSet currCSet =  mCSet.clone();
//		IntSet currSSet =  mSSet.clone();
//		IntSet currBSet =  mBSet.clone();
//		/*
//		 * If q in B\F, then tr(q, a) is not empty
//		 */
//		IntSet F = mOperand.getFinalStates();
//		IntSet bMinusF =  currBSet.clone();
//		bMinusF.andNot(F); 
//		IntIterator iter = bMinusF.iterator();
//		while(iter.hasNext()) {
//			if (mOperand.getSuccessors(iter.next(), letter).isEmpty()) {
//				return UtilIntSet.newIntSet();
//			}
//		}
//		// should have successors
//		
//		/* -------------- compute successors -----------------*/
//		IntSet NSuccs = mOperand.getSuccessors(currNSet, letter);
//		IntSet CSuccs = mOperand.getSuccessors(currCSet, letter);
//		IntSet SSuccs = mOperand.getSuccessors(currSSet, letter);
//		IntSet BSuccs = mOperand.getSuccessors(currBSet, letter);
//		
//		// record used transition (NOT necessary in complement)
//		mComplement.useOpTransition(letter, currNSet);
//		mComplement.useOpTransition(letter, currCSet);
//		mComplement.useOpTransition(letter, currSSet);
//		/* ------------------------------------------------*/
//		
//		boolean bIsEmpty = currBSet.isEmpty();
//		// N successors
//		IntSet Np =  NSuccs.clone();
//				
//		Np.andNot(F);            // remove final states
//		Np.andNot(CSuccs);       // remove successors of C, the final states of NSuccs are in CSuccs 
//		Np.andNot(SSuccs);       // remove successors of S
//		
//		// C successors, V'
//		IntSet Cp =  CSuccs.clone();
//		IntSet nInterF =  NSuccs.clone();
//		nInterF.and(F);
//		Cp.or(nInterF);
//		
//		// S successors
//		IntSet Sp =  SSuccs.clone();
//		
//		// B successors
//		IntSet Bp =  BSuccs.clone();
//		
//		
//		/* -------------- compute word distribution to S' -----------------*/
//		//  compute successors which can be added into S'
//		IntSet mayIns = null;
//		if(bIsEmpty) {
//			// mustNots, must in C' d(N)/\F
//			mayIns = CSuccs.clone();
//			// may also delete states in CSuccs, I think we should move them to S
//			// V'\(d(N)/\F), which may be in C'
//			mayIns.andNot(nInterF); 
//		}else {
//			// set to empty
//			IntSet bInterF = currBSet.clone();
//			bInterF.and(F);
//			// d(B/\F)  M'
//			mayIns = mOperand.getSuccessors(bInterF, letter);
//			// OPTIMIZATION, keep all d(B\F) successors
//			IntSet bMinusFSuccs = mOperand.getSuccessors(bMinusF, letter);
//			mayIns.andNot(bMinusFSuccs);
//		}
//
////		System.out.println(CInterFSuccs);
//		PowerSet ps = new PowerSet(mayIns);
//												
//		while (ps.hasNext()) {
//			IntSet extra = ps.next(); // extra states to be added into S'
////			if(Sextra.overlap(mustNots)) continue;
//			
//			IntSet NPrime = Np;
//			IntSet CPrime = null;
//			IntSet SPrime = Sp.clone();
//			IntSet BPrime = null;
//
//			if(bIsEmpty) {
//				// as usual S and C
//				CPrime = nInterF.clone();
//				CPrime.or(extra); // C' get extra
//				BPrime = CPrime.clone(); // B'= C'
//				IntSet temp = CSuccs.clone(); // V'
//				temp.andNot(CPrime); // V'\C'
//				SPrime.or(temp); // S'=d(S)\/(V'\C')
//
//			}else {
//				// B is not empty
//				if(Options.optNCSB1) {
//					SPrime.or(extra);      //d(S) \/ M'
//					BPrime = Bp.clone();
//					BPrime.andNot(extra); // B'=d(B)\M'
//					CPrime = Cp.clone();   // V'
//					CPrime.andNot(SPrime); // C'= V'\S'
//				}else {
//					SPrime.or(extra);      //d(S) \/ M'
//					CPrime = Cp.clone();   // V'
//					CPrime.andNot(SPrime); // C'= V'\S'
//					BPrime = Bp.clone();
//					BPrime.and(CPrime);
//					BPrime.andNot(extra); // B'=(d(B)/\C')\M'
//				}
//
//			}
//
//			// make sure S' /\ F and B' /\ S' are empty
//			if (!SPrime.overlap(F) && !BPrime.overlap(SPrime)) {
//				StateNCSB succ = mComplement.addState(NPrime, CPrime, SPrime, BPrime);
//				this.addSuccessor(letter, succ.getId());
////				succs.add(succ);
//			}
//		}
//
//		return super.getSuccessors(letter);
//	}
//	

////	@Override
//	public IntSet getSuccessors2(int letter) {
//		
//		Set<StateNCSB> succs = new HashSet<>();
//		
//		if(visitedLetters.get(letter)) {
//			return super.getSuccessors(letter);
//		}
//		
//		visitedLetters.set(letter);
//		
//		IntSet currNSet =  mNSet.clone();
//		IntSet currCSet =  mCSet.clone();
//		IntSet currSSet =  mSSet.clone();
//		IntSet currBSet =  mBSet.clone();
//		/*
//		 * If q in C\F, then tr(q, a) is not empty
//		 */
//		boolean wrong = false;
//		IntSet F = mOperand.getFinalStates();
//		IntSet cMinusF =  currCSet.clone();
//		cMinusF.andNot(F); 
//		for (int s = cMinusF.nextSetBit(0); s >= 0; s = cMinusF.nextSetBit(s + 1)) {
//			if (mOperand.getSuccessors(s, letter).isEmpty()) {
//				wrong = true;
//				break;
//			}
//		}// should have successors
//		
//		// if guess is wrong, then empty
//		if (wrong) return new IntSet();
//		
//		/* -------------- compute B' of B -----------------*/
//		IntSet BSuccs = mOperand.getSuccessors(currBSet, letter);
//		/* ------------------------------------------------*/
//		
//		/* -------------- compute S' of S -----------------*/
//		IntSet SSuccs = mOperand.getSuccessors(currSSet, letter);
//
//		/* ------------------------------------------------*/
//		
//		/* -------------- compute C' of C -----------------*/
//		// firstly compute successors of C\F which must be in C'
//		IntSet CMinusFSuccs = mOperand.getSuccessors(cMinusF, letter);
//		
//		// secondly compute successors of C/\ F which may have final states
//		IntSet cIntersectF = UtilIntSet.intersect(currCSet, F);             // get all accepting states in C
//		IntSet CInterFSuccs = mOperand.getSuccessors(cIntersectF, letter);  // get successors of accepting states
//		
//		// now we get all successors of C
//		IntSet CSuccs = new IntSet();
//		CSuccs.or(CMinusFSuccs);                        // add successors of C\F
//		CSuccs.or(CInterFSuccs);                        // add successors of C/\F
//		
//		// note that we should remove all final states which may go to S'
//		CInterFSuccs.andNot(F);                            // remove accepting state here
//		
//		/* ------------------------------------------------*/
//
//		/* -------------- compute N' of N -----------------*/
//		IntSet NSuccs = mOperand.getSuccessors(currNSet, letter); // add successors of N
//		IntSet tmp =  NSuccs.clone();
//		tmp.andNot(F);
//		CSuccs.or(tmp); // add final successors in C
//		
//		NSuccs.andNot(F);            // remove final states
//		NSuccs.andNot(CSuccs);       // remove successors of C, the final states of NSuccs are in CSuccs 
//		NSuccs.andNot(SSuccs);       // remove successors of S
//		/* ------------------------------------------------*/
//
//		/* ----------- make nondeterministic choices ------------------- */
//		// the successors of C /\ F should go to C and S with nondeterministic choices
//		CInterFSuccs.andNot(CMinusFSuccs);         // remove must-in C states
////		System.out.println(CInterFSuccs);
//		PowerSet ps = new PowerSet(CInterFSuccs); 
//												
//		while (ps.hasNext()) {
//			IntSet Sextra = ps.next(); // extra states to be added into S'
//
//			IntSet NPrime = NSuccs;
//			IntSet CPrime =  CSuccs.clone();
//			CPrime.andNot(Sextra);
//			IntSet SPrime =  SSuccs.clone();
//			SPrime.or(Sextra);
//			
//			IntSet BPrime = null;
//			if(currBSet.isEmpty() ) {
//				BPrime =  CPrime.clone();
//			}else {
//				BPrime =  BSuccs.clone();
//				BPrime.andNot(Sextra);
//			}
//
//			if (hasNoOverlap(SPrime, F) && hasNoOverlap(CPrime, SPrime)) {
//				StateNCSB succ = mComplement.addState(NPrime, CPrime, SPrime, BPrime);
//				this.addSuccessor(letter, succ.getId());
//				succs.add(succ);
//			}
//		}
//
//		return super.getSuccessors(letter);
//	}
	

}
