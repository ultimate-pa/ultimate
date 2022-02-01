/*
 * Copyright (C) 2012-2015 Evren Ermis
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;


/**
 * Rename signature procedures specification n a way that it is compatible to
 * the implementation of the procedure. E.g. we have specification <br>
 * {@code procedure foo(x:int) returns (y:bool);}<br>
 * and an implementation<br>
 * {@code implementation foo(a:int) returns (b:bool)}<br>
 * then this class can be used to obtain a specification where x is renamed to a
 * and y is renamed to b.<br>
 * {@code procedure foo(x:int) returns (y:bool);}
 */
public class RenameProcedureSpec extends BoogieTransformer {
	HashMap<String, String> mRenaming;
	
	public void buildRenaming(final VarList[] specVars, final VarList[] implVars) {
		int j1 = 0, j2 = 0;
		String[] implIds = new String[0];

		/* Iterate through all spec variables */
		for (int i1 = 0; i1 < specVars.length; i1++) {
			final String[] specIds = specVars[i1].getIdentifiers();
			for (int i2 = 0; i2 < specIds.length; i2++) {

				/* Find next implementation variable */
				while (j2 == implIds.length) {
					implIds = implVars[j1++].getIdentifiers();
					j2 = 0;
				}
				
				assert specVars[i1].getType().getBoogieType()
					.equals(implVars[j1-1].getType().getBoogieType());
				if (!specIds[i2].equals(implIds[j2])) {
					mRenaming.put(specIds[i2], implIds[j2]);
				}
				j2++;
			}
		}
	}
	
	public Specification[] renameSpecs(final Procedure proc, final Procedure impl) {
		final Specification[] oldSpecs = proc.getSpecification();
		final Specification[] specs = oldSpecs.clone();
		boolean changed = false;

		/* Put the input variables into renaming */
		mRenaming = new HashMap<>();
		buildRenaming(proc.getInParams(), impl.getInParams());
		if (!mRenaming.isEmpty()) {
			/* Process the requires specifications only on in variables */
			for (int i = 0; i < specs.length; i++) {
				if (specs[i] instanceof RequiresSpecification) {
					specs[i] = processSpecification(specs[i]);
					if (specs[i] != oldSpecs[i]) {
						changed = true;
					}
				}
			}
		}

		/* Now add the output variables to renaming */
		buildRenaming(proc.getOutParams(), impl.getOutParams());
		if (!mRenaming.isEmpty()) {
			/* Process the ensures specifications only on in and out variables */
			for (int i = 0; i < specs.length; i++) {
				if (specs[i] instanceof EnsuresSpecification) {
					specs[i] = processSpecification(specs[i]);
					if (specs[i] != oldSpecs[i]) {
						changed = true;
					}
				}
			}
		}
		mRenaming = null;
		return changed ? specs : oldSpecs;
	}
	
	@Override
	public Expression processExpression(final Expression expr) {
		/* TODO: handle name conflicts in quantifiers */
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression id = (IdentifierExpression) expr;
			final String newName = mRenaming.get(id.getIdentifier());
			if (newName != null) {
			    final IdentifierExpression newExpr = new IdentifierExpression(
			    		expr.getLocation(), expr.getType(), newName,
			    		id.getDeclarationInformation());
			    ModelUtils.copyAnnotations(expr, newExpr);
			    return newExpr;
			}
			return expr;
		}
		return super.processExpression(expr);
	}
}
