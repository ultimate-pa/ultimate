/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 * 
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class TrueWitnessGenerator extends BaseObserver {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public TrueWitnessGenerator(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof RootNode) {
			doit((RootNode) root);
		}
		return false;
	}

	private void doit(final RootNode root) {
		final RootAnnot rootAnnot = root.getRootAnnot();
		final IBacktranslationService backtranslator = mServices.getBacktranslationService();
		final Term trueTerm = rootAnnot.getScript().term("true");

		for (final ProgramPoint locNode : rootAnnot.getLoopLocations().keySet()) {
			assert (locNode.getBoogieASTNode() != null) : "locNode without BoogieASTNode";

			final HoareAnnotation hoare = HoareAnnotation.getAnnotation(locNode);
			if (hoare == null) {
				continue;
			}
			final Term formula = hoare.getFormula();
			if (formula.equals(trueTerm)) {
				continue;
			}

			final Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
			mLogger.info("Invariant at " + locNode + " is "
					+ backtranslator.translateExpressionToString(expr, (Class<Expression>) expr.getClass()));
			// InvariantResult<RcfgElement, Expression> invResult = new InvariantResult<RcfgElement, Expression>(
			// Activator.s_PLUGIN_NAME, locNode, translator_sequence, expr);
		}

		for (final Entry<String, ProgramPoint> entry : rootAnnot.getExitNodes().entrySet()) {
			if (isAuxilliaryProcedure(entry.getKey())) {
				continue;
			}
			final HoareAnnotation hoare = HoareAnnotation.getAnnotation(entry.getValue());
			if (hoare == null) {
				continue;
			}
			final Term formula = hoare.getFormula();
			if (formula.equals(trueTerm)) {
				continue;
			}
			final Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
			mLogger.info("Contract at " + entry.getValue() + " is "
					+ backtranslator.translateExpressionToString(expr, (Class<Expression>) expr.getClass()));

			// ProcedureContractResult<RcfgElement, Expression> result = new ProcedureContractResult<RcfgElement,
			// Expression>(
			// Activator.s_PLUGIN_NAME, finalNode, translator_sequence, proc, expr);
		}
	}

	private static boolean isAuxilliaryProcedure(final String proc) {
		return proc.equals("ULTIMATE.init") || proc.equals("ULTIMATE.start");
	}

}
