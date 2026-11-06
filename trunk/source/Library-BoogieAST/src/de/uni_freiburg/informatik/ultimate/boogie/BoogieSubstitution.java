/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE BoogieAST Library.
 *
 * The ULTIMATE BoogieAST Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieAST Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieAST Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieAST Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieAST Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/**
 * Substitutes free variables by given expressions, in a Boogie expression.
 *
 * Capturing and substitution of bound variables is avoided by alpha-renaming quantified variables where needed.
 */
public class BoogieSubstitution extends BoogieTransformer {
	private final Map<String, ? extends Expression> mSubstitutionMap;
	private final Set<String> mAffectedVariables;

	public BoogieSubstitution(final Map<String, ? extends Expression> substitutionMap) {
		mSubstitutionMap = Objects.requireNonNull(substitutionMap);
		mAffectedVariables = affectedVariables(mSubstitutionMap);
	}

	@Override
	public Expression processExpression(final Expression expr) {
		if (expr instanceof final IdentifierExpression idExpr && mSubstitutionMap.containsKey(idExpr.getIdentifier())) {
			return mSubstitutionMap.get(idExpr.getIdentifier());
		}
		if (expr instanceof final QuantifierExpression quantExpr) {
			return processQuantifierExpression(quantExpr);
		}

		return super.processExpression(expr);
	}

	private Expression processQuantifierExpression(final QuantifierExpression quantExpr) {
		final var freeMatrixVariables = freeVariables(quantExpr.getSubformula()).collect(Collectors.toSet());
		final var alphaRenaming = getAlphaRenaming(quantExpr.getParameters(), freeMatrixVariables);
		if (alphaRenaming.isEmpty()) {
			return super.processExpression(quantExpr);
		}

		final var renamingSubst = new BoogieSubstitution(alphaRenaming);
		final var renamedSubformula = renamingSubst.processExpression(quantExpr.getSubformula());
		final var renamedAttributes = renamingSubst.processAttributes(quantExpr.getAttributes());
		final var renamedParameters = renamingSubst.processVarLists(rename(alphaRenaming, quantExpr.getParameters()));
		final var renamedExpr = new QuantifierExpression(quantExpr.getLocation(), quantExpr.isUniversal(),
				quantExpr.getTypeParams(), renamedParameters, renamedAttributes, renamedSubformula);
		ModelUtils.copyAnnotations(quantExpr, renamedExpr);

		return super.processExpression(renamedExpr);
	}

	private Map<String, IdentifierExpression> getAlphaRenaming(final VarList[] boundVariables,
			final Set<String> freeMatrixVariables) {
		final Set<String> usedVariables = new HashSet<>(freeMatrixVariables);
		usedVariables.addAll(mAffectedVariables);

		final var result = new HashMap<String, IdentifierExpression>();

		for (final var vl : boundVariables) {
			for (final var variable : vl.getIdentifiers()) {
				if (!mAffectedVariables.contains(variable)) {
					continue;
				}

				final var newVariable = getFreeRename(variable, usedVariables);
				result.put(variable, new IdentifierExpression(vl.getLocation(), vl.getType().getBoogieType(),
						newVariable, DeclarationInformation.DECLARATIONINFO_QUANTIFIED));
				usedVariables.add(newVariable);
			}
		}

		return result;
	}

	private static String getFreeRename(final String currentName, final Set<String> usedNames) {
		int cnt = 0;
		while (usedNames.contains(currentName + "$" + cnt)) {
			cnt++;
		}
		return currentName + "$" + cnt;
	}

	private static VarList[] rename(final Map<String, IdentifierExpression> alphaRenaming, final VarList[] original) {
		return Arrays.stream(original).map(vl -> rename(alphaRenaming, vl)).toArray(VarList[]::new);
	}

	private static VarList rename(final Map<String, IdentifierExpression> alphaRenaming, final VarList original) {
		final var newIdentifiers = Arrays.stream(original.getIdentifiers()).<String> map(
				id -> alphaRenaming.get(id) instanceof final IdentifierExpression idExpr ? idExpr.getIdentifier() : id)
				.toArray(String[]::new);
		final var newVl = new VarList(original.getLocation(), newIdentifiers, original.getType());
		ModelUtils.copyAnnotations(original, newVl);
		return newVl;
	}

	private static Set<String> affectedVariables(final Map<String, ? extends Expression> substitutionMap) {
		return Stream
				.concat(substitutionMap.keySet().stream(),
						substitutionMap.values().stream().flatMap(BoogieSubstitution::freeVariables))
				.collect(Collectors.toSet());
	}

	private static Stream<String> freeVariables(final Expression expr) {
		return new BoogieVariableCollector(expr, false, false, true).collectedOccurences().stream()
				.map(occ -> occ.identifier());
	}
}
