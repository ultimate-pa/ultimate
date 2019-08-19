/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

public class ScopedBoogieVarBuilder {

	private final BoogieSymbolTable mSymbolTable;
	private final Hashtable<VariableUID, ScopedBoogieVar> mVarCache;

	public ScopedBoogieVarBuilder(final BoogieSymbolTable table) {
		mSymbolTable = table;
		mVarCache = new Hashtable<>();
	}

	public ScopedBoogieVar getScopedBoogieVar(final VariableLHS lhs, final UnmodifiableTransFormula tf) {
		return getScopedBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), tf);
	}

	public ScopedBoogieVar getScopedBoogieVar(final IdentifierExpression identifier, final UnmodifiableTransFormula tf) {
		return getScopedBoogieVar(identifier.getIdentifier(), identifier.getDeclarationInformation(), tf);

	}

	private ScopedBoogieVar getScopedBoogieVar(final String identifier, final DeclarationInformation info, final UnmodifiableTransFormula tf) {
		final VariableDeclaration decl = (VariableDeclaration) mSymbolTable.getDeclaration(identifier,
				info.getStorageClass(), info.getProcedure());
		final VariableUID uid = new VariableUID(decl, identifier);

		ScopedBoogieVar rtr = mVarCache.get(uid);
		if (rtr == null) {
			final IProgramVar bv = getBoogieVarFromTransformula(identifier, info, tf);
			rtr = new ScopedBoogieVar(identifier, decl, info, bv);
			mVarCache.put(uid, rtr);
		}
		return rtr;
	}

	private IProgramVar getBoogieVarFromTransformula(final String identifier, final DeclarationInformation info, final UnmodifiableTransFormula tf) {
		// TODO: Check if this is the "right" way to get the correct BoogieVar

		final HashSet<IProgramVar> vars = new HashSet<IProgramVar>();
		vars.add(getBoogieVarFromSet(identifier, info, tf.getInVars().keySet()));
		vars.add(getBoogieVarFromSet(identifier, info, tf.getOutVars().keySet()));
		vars.add(getBoogieVarFromSet(identifier, info, tf.getAssignedVars()));
		vars.remove(null);

		if (vars.size() != 1) {
			throw new UnsupportedOperationException("Could not find matching BoogieVar");
		}
		return vars.iterator().next();
	}

	private IProgramVar getBoogieVarFromSet(final String identifier, final DeclarationInformation info, final Set<IProgramVar> vars) {
		for (final IProgramVar in : vars) {
			if (in instanceof ILocalProgramVar) {
				if (((ILocalProgramVar) in).getIdentifier().equals(identifier)) {
					return in;
				}
			} else if (in instanceof IProgramNonOldVar) {
				if (((ILocalProgramVar) in).getIdentifier().equals(identifier)) {
					return in;
				}
			} else if (in instanceof IProgramOldVar) {
				continue;
			} else {
				throw new UnsupportedOperationException("unknown king of IProgramVarIProgramVar " + in.getClass().getSimpleName());
			}
		}
		return null;
	}

	private class VariableUID {

		private final VariableDeclaration Declaration;
		private final String Identifier;

		public VariableUID(final VariableDeclaration decl, final String ident) {
			Declaration = decl;
			Identifier = ident;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((Declaration == null) ? 0 : Declaration.hashCode());
			result = prime * result + ((Identifier == null) ? 0 : Identifier.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final VariableUID other = (VariableUID) obj;
			if (!getOuterType().equals(other.getOuterType())) {
				return false;
			}
			if (Declaration == null) {
				if (other.Declaration != null) {
					return false;
				}
			} else if (!Declaration.equals(other.Declaration)) {
				return false;
			}
			if (Identifier == null) {
				if (other.Identifier != null) {
					return false;
				}
			} else if (!Identifier.equals(other.Identifier)) {
				return false;
			}
			return true;
		}

		private ScopedBoogieVarBuilder getOuterType() {
			return ScopedBoogieVarBuilder.this;
		}
	}

}
