package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;

public class ImpRootAnnot extends RootAnnot {
	
	private static final long serialVersionUID = 1L;
	
//	HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>> callPredToReturnPreds;

	public ImpRootAnnot(Boogie2SMT m_Boogie2smt,
			Backtranslator backtranslator) { //, HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>> callPredToReturnPreds) {
		super(m_Boogie2smt, backtranslator);
//		this.callPredToReturnPreds = callPredToReturnPreds;
	}

//	HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>> getCallPredToReturnPreds() {
//		return callPredToReturnPreds;
//	}
}
