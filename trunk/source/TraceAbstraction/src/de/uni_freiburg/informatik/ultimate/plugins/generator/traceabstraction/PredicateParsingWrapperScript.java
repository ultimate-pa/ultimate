/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.WrapperScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * While parsing {@link IPredicate}s from strings we use an object of this class to wrap the default {@link Script}. Our
 * term parser does not support {@link TermVariables} and tries to match every identifier with a (possibly 0-ary)
 * function symbol by calling the {@link Script#term} method. The term method of this class first tries to match the
 * identifier with identifiers of default TermVariables of {@link IProgramVar}s
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PredicateParsingWrapperScript extends WrapperScript {

	private final Map<String, TermVariable> mProgramVarId2Tv;

	public PredicateParsingWrapperScript(final CfgSmtToolkit csToolkit) {
		super(csToolkit.getManagedScript().getScript());
		mProgramVarId2Tv = new HashMap<>();
		final Set<IProgramVar> programVars = IcfgUtils.collectAllProgramVars(csToolkit);
		for (final IProgramVar pv : programVars) {
			final TermVariable tv = pv.getTermVariable();
			mProgramVarId2Tv.put(tv.getName(), tv);
		}
	}

	@Override
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		if (params.length == 0 && mProgramVarId2Tv.containsKey(funcname)) {
			return mProgramVarId2Tv.get(funcname);
		}
		return mScript.term(funcname, params);
	}

	@Override
	public Term term(final String funcname, final BigInteger[] indices, final Sort returnSort, final Term... params)
			throws SMTLIBException {
		if (params.length == 0 && mProgramVarId2Tv.containsKey(funcname)) {
			return mProgramVarId2Tv.get(funcname);
		}
		return mScript.term(funcname, indices, returnSort, params);
	}
}
