package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;

public class IcfgAngelicProgramExecution extends IcfgProgramExecution {
	
	private boolean mAngelicStatus;

	public IcfgAngelicProgramExecution(final IcfgProgramExecution programExecution, final boolean angelicStatus) {
		super(programExecution);
		mAngelicStatus = angelicStatus;
		
	}
	public boolean getAngelicStatus() {
		return mAngelicStatus;
	}

}
