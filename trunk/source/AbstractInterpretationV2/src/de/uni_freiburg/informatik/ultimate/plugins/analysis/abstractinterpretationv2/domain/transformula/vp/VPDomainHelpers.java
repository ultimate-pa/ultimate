package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;


import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPDomainHelpers {
//	public static IProgramVar getIProgramVarFromTermVariable(TermVariable tv, TransFormula tf) {
//		for (Entry<IProgramVar, TermVariable> en : tf.getInVars().entrySet()) {
//			if (en.getValue() == tv) {
//				return en.getKey();
//			}
//		}
//		for (Entry<IProgramVar, TermVariable> en : tf.getOutVars().entrySet()) {
//			if (en.getValue() == tv) {
//				return en.getKey();
//			}
//		}
//		assert false : "should not happen";
//		return null;
//	}
	
	public static Map<TermVariable, IProgramVar> computeProgramVarMappingFromTransFormula(TransFormula tf) {
		Map<TermVariable, IProgramVar> result = new HashMap<>();
		for (Entry<IProgramVar, TermVariable> en : tf.getInVars().entrySet()) {
			result.put(en.getValue(), en.getKey());
		}
		for (Entry<IProgramVar, TermVariable> en : tf.getOutVars().entrySet()) {
			result.put(en.getValue(), en.getKey());
		}
		return result;
	}
}
