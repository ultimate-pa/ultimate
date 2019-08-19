/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;

/**
 * Specifies properties of a state in a graph representation of a system. These properties are
 * <ul>
 * <li>Name of a location mLocationName</li>
 * <li>Name of a procedure mProcedureName</li>
 * <li>Possible valuations of variables in this state mStateFormulas</li>
 * </ul>
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class HoareAnnotation extends SPredicate {

	private static final String KEY = HoareAnnotation.class.getSimpleName();
	private static final long serialVersionUID = 72852101509650437L;

	private final Script mScript;
	@Visualizable
	private final boolean mIsUnknown = false;

	private final List<Term> mInvariants = new ArrayList<>();

	public HoareAnnotation(final IcfgLocation programPoint, final int serialNumber,
			final PredicateFactory predicateFactory, final Script script) {
		super(programPoint, serialNumber, new String[] { programPoint.getProcedure() }, script.term("true"),
				new HashSet<IProgramVar>(), null);
		mScript = script;
	}

	public void addInvariant(final IPredicate pred) {
		mVars.addAll(pred.getVars());
		mInvariants.add(pred.getFormula());
	}

	@Override
	public Term getFormula() {
		return SmtUtils.and(mScript, mInvariants);
	}

	@Override
	public Term getClosedFormula() {
		return PredicateUtils.computeClosedFormula(getFormula(), mVars, mScript);
	}

	@Override
	public boolean isUnknown() {
		return mIsUnknown;
	}

	public void annotate(final IElement node) {
		if (node == null) {
			return;
		}
		node.getPayload().getAnnotations().put(KEY, this);
	}

	public static HoareAnnotation getAnnotation(final IElement node) {
		if (node != null && node.hasPayload()) {
			final IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				final IAnnotations annot = payload.getAnnotations().get(KEY);
				if (annot != null) {
					return (HoareAnnotation) annot;
				}
			}
		}
		return null;
	}

}
