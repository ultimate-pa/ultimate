package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.FormulaToEqDisjunctiveConstraintConverter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.WeqSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;

public class EqDomain extends StateBasedDomain<EqState> {
	private final IUltimateServiceProvider mServices;
	private final EqConstraintFactory<EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqFactory;

	public EqDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout, final IUltimateServiceProvider services) {
		super(logger, tools, maxDisjuncts, timeout);
		mServices = services;
		mEqFactory = new EqNodeAndFunctionFactory(services, mTools.getManagedScript(), Set.of(), null, Set.of());
		mEqConstraintFactory = new EqConstraintFactory<>(mEqFactory, services, mTools.getManagedScript(),
				new WeqSettings(), false, Set.of());
	}

	@Override
	protected List<EqState> toStates(final IPredicate pred) {
		final EqDisjunctiveConstraint<EqNode> converted = new FormulaToEqDisjunctiveConstraintConverter(mServices,
				mTools.getManagedScript(), mEqConstraintFactory, mEqFactory, pred.getFormula()).getResult();
		// TODO join disjuncts if there are too many of them
		return converted.getConstraints().stream().map(EqState::new).collect(Collectors.toList());
	}
}
