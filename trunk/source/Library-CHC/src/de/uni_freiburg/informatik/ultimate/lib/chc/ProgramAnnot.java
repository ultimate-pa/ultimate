package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class ProgramAnnot extends BasePayloadContainer {
	private static final long serialVersionUID = -6722896725096551522L;

	private final Model mModel;

	public ProgramAnnot(final Model model) {
		mModel = model;
	}

	public Term getFormula(final List<IcfgLocation> locactions,
			final List<Map<IProgramVar, Term>> localVarSubstitutions) {
		return mModel.getFunctionDefinition(getFunctionSymbol(locactions),
				getArguments(locactions, localVarSubstitutions));
	}

	protected abstract String getFunctionSymbol(List<IcfgLocation> locactions);

	protected abstract Term[] getArguments(List<IcfgLocation> locactions,
			List<Map<IProgramVar, Term>> localVarSubstitutions);
}
