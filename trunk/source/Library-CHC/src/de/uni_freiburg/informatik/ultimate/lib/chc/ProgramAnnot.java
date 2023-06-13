package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
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
			final BiFunction<IProgramVar, Integer, Term> localVarProvider, final ManagedScript managedScript,
			final IUltimateServiceProvider services) {
		final Term[] args = getArguments(locactions, localVarProvider);
		final TermVariable[] tmpArgs = new TermVariable[args.length];
		final Map<Term, Term> substitution = new HashMap<>();
		for (int i = 0; i < args.length; i++) {
			tmpArgs[i] = managedScript.constructFreshTermVariable("x", args[i].getSort());
			substitution.put(tmpArgs[i], args[i]);
		}
		final Term modelAsTerm = mModel.getFunctionDefinition(getFunctionSymbol(locactions), tmpArgs);
		final Term substituted = Substitution.apply(managedScript, substitution, modelAsTerm);
		return SmtUtils.simplify(managedScript, substituted, services, SimplificationTechnique.POLY_PAC);
	}

	protected abstract String getFunctionSymbol(List<IcfgLocation> locactions);

	protected abstract Term[] getArguments(List<IcfgLocation> locactions,
			BiFunction<IProgramVar, Integer, Term> localVarProvider);

	// TODO: How should we indicate that a thread is not started, by providing lists of different sizes?
	protected abstract Collection<List<IcfgLocation>> getReachableProductLocations();

	public Map<List<IcfgLocation>, Term> toProductMap(final BiFunction<IProgramVar, Integer, Term> localVarProvider,
			final ManagedScript managedScript, final IUltimateServiceProvider services) {
		return getReachableProductLocations().stream()
				.collect(Collectors.toMap(x -> x, x -> getFormula(x, localVarProvider, managedScript, services)));
	}

	// TODO: Add a method to create an Ashcroft invariant
}
