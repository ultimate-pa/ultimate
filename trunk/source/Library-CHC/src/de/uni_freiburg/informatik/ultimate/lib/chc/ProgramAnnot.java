package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

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
			final BiFunction<IProgramVar, Integer, Term> localVarProvider) {
		return mModel.getFunctionDefinition(getFunctionSymbol(locactions), getArguments(locactions, localVarProvider));
	}

	protected abstract String getFunctionSymbol(List<IcfgLocation> locactions);

	protected abstract Term[] getArguments(List<IcfgLocation> locactions,
			BiFunction<IProgramVar, Integer, Term> localVarProvider);

	// TODO: How should we indicate that a thread is not started, by providing lists of different sizes?
	protected abstract Collection<List<IcfgLocation>> getReachableProductLocations();

	public Map<List<IcfgLocation>, Term> toProductMap(final BiFunction<IProgramVar, Integer, Term> localVarProvider) {
		return getReachableProductLocations().stream()
				.collect(Collectors.toMap(x -> x, x -> getFormula(x, localVarProvider)));
	}

	// TODO: Add a method to create an Ashcroft invariant
}
