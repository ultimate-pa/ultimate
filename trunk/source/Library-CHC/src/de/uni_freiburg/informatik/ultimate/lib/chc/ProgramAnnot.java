package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public abstract class ProgramAnnot extends BasePayloadContainer {
	private static final long serialVersionUID = -6722896725096551522L;

	private final Model mModel;

	public ProgramAnnot(final Model model) {
		mModel = model;
	}

	public Term getFormula(final List<IcfgLocation> locactions,
			final BiFunction<IProgramVar, Integer, TermVariable> localVarProvider, final ManagedScript managedScript) {
		final Term modelAsTerm =
				mModel.getFunctionDefinition(getFunctionSymbol(locactions), getDefaultArguments(localVarProvider));
		return Substitution.apply(managedScript, getSubstitution(locactions), modelAsTerm);
	}

	protected abstract TermVariable[]
			getDefaultArguments(BiFunction<IProgramVar, Integer, TermVariable> localVarProvider);

	protected abstract String getFunctionSymbol(List<IcfgLocation> locactions);

	protected abstract Map<Term, Term> getSubstitution(List<IcfgLocation> locactions);

	// TODO: How should we indicate that a thread is not started, by providing lists of different sizes?
	protected abstract Collection<List<IcfgLocation>> getReachableProductLocations();

	public Map<List<IcfgLocation>, Term> toProductMap(
			final BiFunction<IProgramVar, Integer, TermVariable> localVarProvider, final ManagedScript managedScript) {
		return getReachableProductLocations().stream()
				.collect(Collectors.toMap(x -> x, x -> getFormula(x, localVarProvider, managedScript)));
	}

	// TODO: Add a method to create an Ashcroft invariant
}
