package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class HeapSepRcfgVisitor extends SimpleRCFGVisitor {
	
	
	/**
	 *  arrayId before separation --> pointerId --> arrayId after separation
	 */
	HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> m_oldArrayToPointerToNewArray;
	/**
	 *  arrayId before separation --> arrayId after separation--> Set of pointerIds
	 */
	HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> m_arrayToPartitions;
	Script m_script;

//	public HeapSepRcfgVisitor(Logger logger, HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> map) {
	public HeapSepRcfgVisitor(Logger logger, HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> map, Script script) {
		super(logger);
		m_oldArrayToPointerToNewArray = map;
		m_script = script;
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
		//TODO: maybe build a TransformulaTransformer??
		
		TransFormula newTf = splitArraysInTransFormula(tf);
		
		
//		TransFormula tfNew = new TransFormula(nt, null, null, null, null, null, null);
//		tf.
		super.level(edge);
	}

	
	private TransFormula splitArraysInTransFormula(TransFormula tf) {

		Map<BoogieVar, TermVariable> oldInVars = tf.getInVars();
		Map<BoogieVar, TermVariable> oldOutVars = tf.getOutVars();
		
		
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
		
//		m_oldArrayToPointerToNewArray
		
		Term newFormula = new ArraySplitter(m_script, m_oldArrayToPointerToNewArray, m_arrayToPartitions, oldInVars, oldOutVars).transform(tf.getFormula());

		
		Map<BoogieVar, TermVariable> newInVars = null;
		Map<BoogieVar, TermVariable> newOutVars = null;
		Set<TermVariable> newAuxVars = null;
		Set<TermVariable> newBranchEncoders = null;
		Infeasibility newInfeasibility = null;
		Term newClosedFormula = null;

		TransFormula result = new TransFormula(newFormula, newInVars, newOutVars, newAuxVars, newBranchEncoders, newInfeasibility, newClosedFormula);
		
		return result;
	}

	public static TermVariable getSplitTermVariable(String arrayName, int splitIndex, Sort sort, Script script) {
		return script.variable(String.format("{}_split_{}", arrayName, splitIndex), sort);
	}
	
	public static BoogieVar getBoogieVarFromTermVar(TermVariable tv, Map<BoogieVar, TermVariable> map) {
		for (Entry<BoogieVar, TermVariable> en : map.entrySet()) {
			if (en.getValue().equals(tv))
				return en.getKey();
		}
		assert false : "did not find " + tv + "in the given map";
		return null;
	}
	/**
 	 *
	 */
	public static class ArraySplitter extends TermTransformer {
		Script m_script;
		Map<BoogieVar, TermVariable> m_inVars;
		Map<BoogieVar, TermVariable> m_outVars;
		
		boolean m_equalsMode = false;

		/**
		 * arrayId (old array) X pointerId -> arrayId (split version)
		 */
		HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> m_arrayToPointerToPartition;
		/**
		 * arrayId (old array) X arrayId (split version) -> Set<pointerId>
		 */
		HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> m_arrayToPartitions;

		
		public ArraySplitter(Script script, 
				HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> arrayToPointerToPartition,
				HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> arrayToPartitions,
				Map<BoogieVar, TermVariable> inVars, Map<BoogieVar, TermVariable> outVars) {
			m_arrayToPointerToPartition = arrayToPointerToPartition;
			m_arrayToPartitions = arrayToPartitions;
			m_script = script;
			m_inVars = inVars;
			m_outVars = outVars;
		}
		
		public ArraySplitter(Script script, 
				HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> arrayToPointerToPartition,
				HashMap<BoogieVar, HashMap<BoogieVar, HashSet<BoogieVar>>> arrayToPartitions,
				Map<BoogieVar, TermVariable> inVars, Map<BoogieVar, TermVariable> outVars, 
				BoogieVar a1Old, BoogieVar a1New, BoogieVar a2Old, BoogieVar a2New) {
			this(script, arrayToPointerToPartition, arrayToPartitions, inVars, outVars);
			m_equalsMode = true;
		}



		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {

			if (appTerm.getFunction().getName().equals("select")
					|| appTerm.getFunction().getName().equals("store")) {
				if (appTerm.getParameters()[0] instanceof TermVariable
						&& appTerm.getParameters()[1] instanceof TermVariable) {
					assert appTerm.getParameters()[0].getSort().isArraySort();

					BoogieVar arrayVar = getBoogieVarFromTermVar(((TermVariable) appTerm.getParameters()[0]), m_inVars); //TODO do inVars suffice??

					HashMap<BoogieVar, BoogieVar> im = m_arrayToPointerToPartition.get(arrayVar);
					if (im != null) {
						BoogieVar ptrName = getBoogieVarFromTermVar(((TermVariable) appTerm.getParameters()[1]), m_inVars); //TODO do inVars suffice??

						TermVariable newVar = im.get(ptrName).getTermVariable(); //FIXME probably replace getTermVariable, here
								//getSplitTermVariable(arrayVar, splitIndex, appTerm.getParameters()[0].getSort(), m_script);

						setResult(m_script.term(appTerm.getFunction().getName(), newVar, appTerm.getParameters()[1]));
					}
				}
			} else if (appTerm.getFunction().getName().equals("=")) {
				if (appTerm.getParameters()[0].getSort().isArraySort()
						&& appTerm.getParameters()[1].getSort().isArraySort()) {

					Term p0 = appTerm.getParameters()[0];
					Term p1 = appTerm.getParameters()[1];

					/*
					 * sanity check:
					 *  if anywhere in the program, the two arrays a and b are equated, their partitionings must be compatible
					 *   i.e., no partition of a may overlap two partitions of b and vice versa
					 */

					//assert partitionsAreCompatible(findArrayId(p0), findArrayId(p1)); TODO: write those methods for the assert..
					BoogieVar a0Id = null;
					BoogieVar a1Id = null;
					
					ArrayList<Term> equationConjunction = new ArrayList<Term>();

					/*
					 * for each partition p of a, which has an intersecting partition q of b:
					 *  equate e1[a_p] = e2[b_q]
					 *  (where e1, e2 may be stores or just array identifiers (something else?).
					 */
//					for (int i = 0; i < m_arrayToPartitions.get(a0Id).size(); i++) {
//						HashSet<String> partA0 = m_arrayToPartitions.get(a0Id).get(i);
//						for (int j = 0; j < m_arrayToPartitions.get(a0Id).size(); j++) {
//							HashSet<String> partA1 = m_arrayToPartitions.get(a1Id).get(j);


					for (Entry<BoogieVar, HashSet<BoogieVar>> a0SplitArrayToPointers : m_arrayToPartitions.get(a0Id).entrySet()) {
						for (Entry<BoogieVar, HashSet<BoogieVar>> a1SplitArrayToPointers : m_arrayToPartitions.get(a1Id).entrySet()) {

							HashSet<BoogieVar> intersection = new HashSet<BoogieVar>(a0SplitArrayToPointers.getValue());
							intersection.retainAll(a1SplitArrayToPointers.getValue());

							if (!intersection.isEmpty()) {
								equationConjunction.add(
										new ArraySplitter(m_script, m_arrayToPointerToPartition, m_arrayToPartitions, m_inVars, m_outVars, 
										a0Id, a0SplitArrayToPointers.getKey(), a1Id, a1SplitArrayToPointers.getKey()).transform(appTerm));
								
							}
						}
					}
					
				
				}

			} else
				super.convertApplicationTerm(appTerm, newArgs);
		}
	}


}
