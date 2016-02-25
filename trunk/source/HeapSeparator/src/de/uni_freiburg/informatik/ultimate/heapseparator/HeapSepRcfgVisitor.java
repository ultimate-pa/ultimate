package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class HeapSepRcfgVisitor extends SimpleRCFGVisitor {
	
	
	// arrayId before separation --> pointerId --> arrayId after separation
//	HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> m_oldArrayToPointerToNewArray;
	HashMap<String, HashMap<String, Integer>> m_oldArrayToPointerToNewArray;
	private Script m_script;

//	public HeapSepRcfgVisitor(Logger logger, HashMap<BoogieVar, HashMap<BoogieVar, BoogieVar>> map) {
	public HeapSepRcfgVisitor(Logger logger, HashMap<String, HashMap<String, Integer>> map, Script script) {
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
		Term t = new ArraySplitter(m_oldArrayToPointerToNewArray, m_script).transform(tf.getFormula());
//		TransFormula tfNew = new TransFormula(nt, null, null, null, null, null, null);
//		tf.
		super.level(edge);
	}

	
	/**
 	 *
	 */
	public static class ArraySplitter extends TermTransformer {
		//		TermVariable mTermVar;
		//		Term mReplacement;
		HashMap<String, HashMap<String, Integer>> m_splitMap;
		Script m_script;

		public ArraySplitter(HashMap<String, HashMap<String, Integer>> map, Script script) {
			m_splitMap = map;
			m_script = script;
		}

		//		public void convert(Term term) {
		////			if (term instanceof ApplicationTerm) {
		////
		////				ApplicationTerm at = (ApplicationTerm) term;
		////
		////				if (at.getFunction().getName().equals("select")) {
		////					if (at.getParameters()[0] instanceof TermVariable
		////							&& at.getParameters()[1] instanceof TermVariable) {
		////						String arrayName = ((TermVariable) at.getParameters()[0]).getName();
		////						HashMap<String, Integer> im = m_splitMap.get(arrayName);
		////						if (im != null) {
		////							String ptrName = ((TermVariable) at.getParameters()[1]).getName();
		////							int splitIndex = im.get(ptrName);
		////							TermVariable newVar = m_script.variable(arrayName + "_split_" + splitIndex, m_script.sort("Int"));
		////							setResult(m_script.term(at.getFunction().getName(), newVar, at.getParameters()[1]));
		////						}
		////					}
		////				} else if (at.getFunction().getName().equals("store")) {
		////					if (at.getParameters()[0] instanceof TermVariable
		////							&& at.getParameters()[1] instanceof TermVariable) {
		////						String arrayName = ((TermVariable) at.getParameters()[0]).getName();
		////						HashMap<String, Integer> im = m_splitMap.get(arrayName);
		////						if (im != null) {
		////							String ptrName = ((TermVariable) at.getParameters()[1]).getName();
		////							int splitIndex = im.get(ptrName);
		////							TermVariable newVar = m_script.variable(arrayName + "_split_" + splitIndex, m_script.sort("Int"));
		////							setResult(m_script.term(at.getFunction().getName(), newVar, at.getParameters()[1]));
		////						}
		////					}
		////				} else {
		////					super.convert(term);
		////				}
		////			} else {
		//				super.convert(term);
		////			}
		//		}

		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			if (appTerm.getFunction().getName().equals("select")) {
				if (appTerm.getParameters()[0] instanceof TermVariable
						&& appTerm.getParameters()[1] instanceof TermVariable) {
					String arrayName = ((TermVariable) appTerm.getParameters()[0]).getName();
					HashMap<String, Integer> im = m_splitMap.get(arrayName);
					if (im != null) {
						String ptrName = ((TermVariable) appTerm.getParameters()[1]).getName();
						int splitIndex = im.get(ptrName);
						TermVariable newVar = m_script.variable(arrayName + "_split_" + splitIndex, m_script.sort("Int"));
						setResult(m_script.term(appTerm.getFunction().getName(), newVar, appTerm.getParameters()[1]));
					}
				}
			} else if (appTerm.getFunction().getName().equals("store")) {
				if (appTerm.getParameters()[0] instanceof TermVariable
						&& appTerm.getParameters()[1] instanceof TermVariable) {
					String arrayName = ((TermVariable) appTerm.getParameters()[0]).getName();
					HashMap<String, Integer> im = m_splitMap.get(arrayName);
					if (im != null) {
						String ptrName = ((TermVariable) appTerm.getParameters()[1]).getName();
						int splitIndex = im.get(ptrName);
						TermVariable newVar = m_script.variable(arrayName + "_split_" + splitIndex, m_script.sort("Int"));
						setResult(m_script.term(appTerm.getFunction().getName(), newVar, appTerm.getParameters()[1]));
					}
				}
			} else
				super.convertApplicationTerm(appTerm, newArgs);
		}
	}
	
}
