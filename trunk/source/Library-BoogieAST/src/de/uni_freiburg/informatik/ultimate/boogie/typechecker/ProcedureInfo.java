/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.typechecker;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;

public class ProcedureInfo {
	private final Procedure declaration;
	private final TypeParameters typeParams;
	private final VariableInfo[] inParams;
	private final VariableInfo[] outParams;
	
	public TypeParameters getTypeParameters() {
		return typeParams;
	}

	public Procedure getDeclaration() {
		return declaration;
	}
	
	public VariableInfo[] getInParams() {
		return inParams;
	}
	
	public VariableInfo[] getOutParams() {
		return outParams;
	}
	
	public ProcedureInfo(Procedure declaration, 
			TypeParameters typeParams, VariableInfo[] inParams, VariableInfo[] outParams) {
		this.declaration = declaration; 
		this.typeParams = typeParams;
		this.inParams = inParams;
		this.outParams = outParams;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(declaration.getIdentifier()).append('<').append(typeParams.getCount());
		sb.append(">(");
		String comma ="";
		for (final VariableInfo vi : inParams) {
			sb.append(comma);
			if (vi.getName() != null) {
				sb.append(vi.getName()).append(":");
			}
			sb.append(vi.getType());
			comma = ",";
		}
		if (outParams.length > 0) {
			sb.append(") returns (");
			comma ="";
			for (final VariableInfo vi : outParams) {
				sb.append(comma);
				if (vi.getName() != null) {
					sb.append(vi.getName()).append(":");
				}
				sb.append(vi.getType());
				comma = ",";
			}
		}
		sb.append(")");
		return sb.toString();
	}
}
