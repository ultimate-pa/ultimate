package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class HeapSepRcfgVisitor extends SimpleRCFGVisitor {
	
	
	/**
	 *  arrayId before separation --> pointerId --> arrayId after separation
	 */
	HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> moldArrayToPointerToNewArray;
	/**
	 *  arrayId before separation --> arrayId after separation--> Set of pointerIds
	 */
	HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> marrayToPartitions;
	Script mscript;

	public HeapSepRcfgVisitor(ILogger logger, HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> map, Script script) {
		super(logger);
		moldArrayToPointerToNewArray = map;
		marrayToPartitions = reverseInnerMap(moldArrayToPointerToNewArray);
		mscript = script;
	}


	private HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> reverseInnerMap(
			HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> map) {
		HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> result = new HashMap<BoogieVar, HashMap<BoogieVar,HashSet<BoogieVar>>>();

		for (Entry<BoogieVar, HashMap<BoogieVar, BoogieVar>> en1 : map.entrySet()) {
			result.put(en1.getKey(), new HashMap<>());
			for (Entry<BoogieVar, BoogieVar> en2 : en1.getValue().entrySet()) {
				HashSet<BoogieVar> pointers = result.get(en1.getKey()).get(en2.getValue());
				if (pointers == null) {
					pointers = new HashSet<BoogieVar>();
					result.get(en1.getKey()).put(en2.getValue(), pointers);
				}
				pointers.add(en2.getKey());
			}
		}
		return result;
	}


	@Override
	public boolean performedChanges() {
		// TODO make smarter?
		return true;
	}

	@Override
	public boolean abortCurrentBranch() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean abortAll() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void level(RCFGEdge edge) {
		if (!(edge instanceof CodeBlock))
			return;
		TransFormula tf = ((CodeBlock) edge).getTransitionFormula();
		
		TransFormula newTf = splitArraysInTransFormula(tf);
		
		((CodeBlock) edge).setTransitionFormula(newTf);
		
		super.level(edge);
	}

	
	private TransFormula splitArraysInTransFormula(TransFormula tf) {

	
		
		// new plan: we don't need a term transformer, here (at least not for the simple cases?..)
		// --> just rename the BoogieVars in the maps
		// insight:
		//   that won't work
		//   example:
		//    "(= x' (+ (select a p) (select a q)))" where p and q don't alias
		//        --> we'll need to duplicate a in outvars in this case..
		// other thing:
		//  "(store (store a q i) p j)" where p and q don't alias
		//   --> is this a problem? Is this even possible?
		
		//cases where arrays may occur, in the SMT theory of arrays:
		// - store
		// - select
		// - equals/distinct
		// example
		//  a' in "(= a' (store a p i))"
		//   
		

		ArraySplitter as = new ArraySplitter(mscript, moldArrayToPointerToNewArray, marrayToPartitions, tf.getInVars(), tf.getOutVars());
		Term newFormula = as.transform(tf.getFormula());
		Map<BoogieVar, TermVariable> newInVars = as.getUpdatedInVars();
		Map<BoogieVar, TermVariable> newOutVars = as.getUpdatedOutVars();
	
		
		Set<TermVariable> newAuxVars = tf.getAuxVars();
		Set<TermVariable> newBranchEncoders = tf.getBranchEncoders();
		Infeasibility newInfeasibility = tf.isInfeasible();
		Term newClosedFormula = tf.getClosedFormula();

		TransFormula result = new TransFormula(newFormula, newInVars, newOutVars, newAuxVars, newBranchEncoders, newInfeasibility, newClosedFormula);
		
		return result;
	}

	public static TermVariable getSplitTermVariable(String arrayName, int splitIndex, Sort sort, Script script) {
		return script.variable(String.format("{}_split_{}", arrayName, splitIndex), sort);
	}
	
	public static BoogieVar getBoogieVarFromTermVar(TermVariable tv, Map<BoogieVar, TermVariable> map1, Map<BoogieVar, TermVariable> map2) {
		for (Entry<BoogieVar, TermVariable> en : map1.entrySet()) {
			if (en.getValue().equals(tv))
				return en.getKey();
		}
		for (Entry<BoogieVar, TermVariable> en : map2.entrySet()) {
			if (en.getValue().equals(tv))
				return en.getKey();
		}
		assert false : "did not find " + tv + " in the given maps";
		return null;
	}
	/**
 	 * Input:
 	 *  maps that say how arrays should be split
 	 *  a term to split arrays in
 	 *  inVar and outVar mappings
 	 * Output:
 	 *  the term where arrays are split
 	 * SideEffect:
 	 *  inVar and outVar mappings are updated according to the splitting
	 */
	public static class ArraySplitter extends TermTransformer {
		Script mscript;
		Map<BoogieVar, TermVariable> minVars;
		Map<BoogieVar, TermVariable> moutVars;
		
		Set<BoogieVar> minVarsToRemove = new HashSet<BoogieVar>();
		Map<BoogieVar, TermVariable> minVarsToAdd = new HashMap<>();
		Set<BoogieVar> moutVarsToRemove = new HashSet<BoogieVar>();
		Map<BoogieVar, TermVariable> moutVarsToAdd = new HashMap<>();
		
		boolean mequalsMode = false;
//		BoogieVar maOld;
		TermVariable maOld;
//		BoogieVar maNew;
		TermVariable maNew;

		/**
		 * arrayId (old array) X pointerId -> arrayId (split version)
		 */
		HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> marrayToPointerToPartition;
		/**
		 * arrayId (old array) X arrayId (split version) -> Set<pointerId>
		 */
		HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> marrayToPartitions;

		
		public ArraySplitter(Script script, 
				HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> arrayToPointerToPartition,
				HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> arrayToPartitions,
				Map<BoogieVar, TermVariable> inVars, Map<BoogieVar, TermVariable> outVars) {
			marrayToPointerToPartition = arrayToPointerToPartition;
			marrayToPartitions = arrayToPartitions;
			mscript = script;
			minVars = inVars;
			moutVars = outVars;
		}

		
		public ArraySplitter(Script script, 
				HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> arrayToPointerToPartition,
				HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> arrayToPartitions,
				Map<BoogieVar, TermVariable> inVars, Map<BoogieVar, TermVariable> outVars, 
				TermVariable aOld, TermVariable aNew
				) {
			this(script, arrayToPointerToPartition, arrayToPartitions, inVars, outVars);
			mequalsMode = true;
			maOld = aOld;
			maNew = aNew;
		}

		@Override
		protected void convert(Term term) {
			if (mequalsMode) {
				//TODO: not sure how robust this is..
				if (term.equals(maOld)) {
					setResult(maNew);
					mequalsMode = false;
					return;
				}
			}
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName().equals("select")
						|| appTerm.getFunction().getName().equals("store")) {

					if (mequalsMode 
							&& appTerm.getFunction().getName().equals("store") 
							&& appTerm.getParameters()[0] instanceof TermVariable) {
						//TODO: not sure how robust this is..
						super.convert(appTerm);
						return;

					} else if (appTerm.getParameters()[0] instanceof TermVariable
							&& appTerm.getParameters()[1] instanceof TermVariable) {
						assert appTerm.getParameters()[0].getSort().isArraySort();

						BoogieVar oldArrayVar = getBoogieVarFromTermVar(((TermVariable) appTerm.getParameters()[0]), minVars, moutVars);

						HashMap<BoogieVar, BoogieVar> im = marrayToPointerToPartition.get(oldArrayVar);
						if (im != null) {
							BoogieVar ptrName = getBoogieVarFromTermVar(((TermVariable) appTerm.getParameters()[1]), minVars, moutVars);

							BoogieVar newArrayVar = im.get(ptrName);

							TermVariable newVar = newArrayVar.getTermVariable(); //FIXME probably replace getTermVariable, here

							Term newTerm = appTerm.getFunction().getName().equals("store") 
									? mscript.term(
											appTerm.getFunction().getName(), 
											newVar, 
											appTerm.getParameters()[1],
											appTerm.getParameters()[2]) 
											: mscript.term(
													appTerm.getFunction().getName(), 
													newVar, 
													appTerm.getParameters()[1]);

											// TODO: do we also need outVars here, sometimes?
											minVarsToRemove.add(oldArrayVar);
											minVarsToAdd.put(newArrayVar, newVar);

											setResult(newTerm);
											return;
						}
					}
				} else if (appTerm.getFunction().getName().equals("=")) {
					if (appTerm.getParameters()[0].getSort().isArraySort()
							&& appTerm.getParameters()[1].getSort().isArraySort()) {

						Term p0 = appTerm.getParameters()[0];
						Term p1 = appTerm.getParameters()[1];

						ArrayFinder af0 = new ArrayFinder();
						af0.transform(p0);
						TermVariable a0Tv = af0.getResult();
						BoogieVar a0Id = getBoogieVarFromTermVar(a0Tv, minVars, moutVars);

						ArrayFinder af1 = new ArrayFinder();
						af1.transform(p1);
						TermVariable a1Tv = af1.getResult();
						BoogieVar a1Id = getBoogieVarFromTermVar(a1Tv, minVars, moutVars);

						/*
						 * sanity check:
						 *  if anywhere in the program, the two arrays a and b are equated, their partitionings must be compatible
						 *   i.e., no partition of a may overlap two partitions of b and vice versa
						 */
						//assert partitionsAreCompatible(findArrayId(p0), findArrayId(p1)); TODO: write those methods for the assert..

						ArrayList<Term> equationConjunction = new ArrayList<Term>();

						/*
						 * for each partition p of a, which has an intersecting partition q of b:
						 *  equate e1[a_p] = e2[b_q]
						 *  (where e1, e2 may be stores or just array identifiers (something else?).
						 */
						for (Entry<BoogieVar, HashSet<BoogieVar>> a0SplitArrayToPointers : marrayToPartitions.get(a0Id).entrySet()) {
							for (Entry<BoogieVar, HashSet<BoogieVar>> a1SplitArrayToPointers : marrayToPartitions.get(a1Id).entrySet()) {

								HashSet<BoogieVar> intersection = new HashSet<BoogieVar>(a0SplitArrayToPointers.getValue());
								intersection.retainAll(a1SplitArrayToPointers.getValue());

								if (!intersection.isEmpty()) {
									BoogieVar a0New = a0SplitArrayToPointers.getKey();
									BoogieVar a1New = a1SplitArrayToPointers.getKey();
									TermVariable a0NewTv = a0New.getTermVariable(); //TODO replace getTermVariable through a unique version
									TermVariable a1NewTv = a1New.getTermVariable(); //TODO replace getTermVariable through a unique version
									equationConjunction.add(
											mscript.term("=", 
													new ArraySplitter(mscript, marrayToPointerToPartition, marrayToPartitions, minVars, moutVars, 
															a0Tv, a0NewTv).transform(appTerm.getParameters()[0]), 
													new ArraySplitter(mscript, marrayToPointerToPartition, marrayToPartitions, minVars, moutVars, 
															a1Tv, a1NewTv).transform(appTerm.getParameters()[1])
													));

									if (minVars.containsKey(a0Id)) {
										minVarsToRemove.add(a0Id);
										minVarsToAdd.put(a0New, a0NewTv);
									} else if (moutVars.containsKey(a0Id)) {
										moutVarsToRemove.add(a0Id);
										moutVarsToAdd.put(a0New, a0NewTv);
									} else
										assert false;

									if (minVars.containsKey(a1Id)) {
										minVarsToRemove.add(a1Id);
										minVarsToAdd.put(a1Id, a1NewTv);
									} else if (moutVars.containsKey(a1Id)) {
										moutVarsToRemove.add(a1Id);
										moutVarsToAdd.put(a1Id, a1NewTv);
									} else
										assert false;

								}
							}
						}
						setResult(mscript.term("and", equationConjunction.toArray(new Term[equationConjunction.size()])));
						return;
					}
				} 
			}

			super.convert(term);
		}

		public HashMap<BoogieVar, TermVariable> getUpdatedInVars() {
			HashMap<BoogieVar, TermVariable> result = new HashMap<BoogieVar, TermVariable>(minVars);
			for (BoogieVar bv : minVarsToRemove) 
				result.remove(bv);
			for (Entry<BoogieVar, TermVariable> en : minVarsToAdd.entrySet()) 
				result.put(en.getKey(), en.getValue());
			return result;
		}
		
		public HashMap<BoogieVar, TermVariable> getUpdatedOutVars() {
			HashMap<BoogieVar, TermVariable> result = new HashMap<BoogieVar, TermVariable>(moutVars);
			for (BoogieVar bv : moutVarsToRemove) 
				result.remove(bv);
			for (Entry<BoogieVar, TermVariable> en : moutVarsToAdd.entrySet()) 
				result.put(en.getKey(), en.getValue());
			return result;
		}

	}


	public static class ArrayFinder extends TermTransformer {
		TermVariable marrayId;
		
		@Override
		protected void convert(Term term) {
			if (term.getSort().isArraySort() && term instanceof TermVariable) {
				marrayId = (TermVariable) term;
				setResult(term);
				return;
			}
			super.convert(term);
		}
	
		TermVariable getResult() {
			return marrayId;
		}
	}
	
	

}
