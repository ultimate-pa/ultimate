/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */

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

/**
 * Extract the invariants per location from a CHC model
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
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

	protected abstract Collection<List<IcfgLocation>> getReachableProductLocations();

	public Map<List<IcfgLocation>, Term> toProductMap(
			final BiFunction<IProgramVar, Integer, TermVariable> localVarProvider, final ManagedScript managedScript) {
		return getReachableProductLocations().stream()
				.collect(Collectors.toMap(x -> x, x -> getFormula(x, localVarProvider, managedScript)));
	}
}
