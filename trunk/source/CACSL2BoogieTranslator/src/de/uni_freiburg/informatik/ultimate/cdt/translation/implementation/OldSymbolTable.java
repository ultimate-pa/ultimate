/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Symbol Table for the compiler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.cdt.parser.MultiparseSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @author Markus Lindenmann
 * @since 13.07.2012
 */
public class OldSymbolTable extends LinkedScopedHashMap<String, SymbolTableValue> {
	/**
	 * Holds a map from BoogieIDs and the corresponding CIDs.
	 */
	private final Map<String, String> mBoogieID2CID;

	private final Map<CDeclaration, Declaration> mCDecl2BoogieDecl;
	/**
	 * unique ID for current scope.
	 */
	private int mCompoundCounter;

	private final Stack<Integer> mCompoundNrStack = new Stack<>();

	/**
	 * A reference to the main dispatcher.
	 */
	private final Dispatcher mMain;

	/**
	 * Constructor.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 */
	public OldSymbolTable(final Dispatcher main) {
		super();
		mBoogieID2CID = new HashMap<>();
		mCDecl2BoogieDecl = new HashMap<>();
		mCompoundCounter = 0;
		mMain = main;
	}

	@Override
	public SymbolTableValue put(final String cId, final SymbolTableValue value) {
		if (!mMain.mTypeHandler.isStructDeclaration()) {
			final SymbolTableValue v = super.put(cId, value);
			mBoogieID2CID.put(value.getBoogieName(), cId);
			mCDecl2BoogieDecl.put(value.getCDecl(), value.getBoogieDecl());
			return v;
		}
		return null;
	}

	/**
	 * @Override
	 * @deprecated ignores the error location! Use <code>get(String, Location)</code> instead.
	 **/
	@Deprecated
	@Override
	public SymbolTableValue get(final Object cId) {
		return get((String) cId, null);
	}

	/**
	 * Returns the SymbolTableValue for the id cId.
	 *
	 * @param cId
	 *            the C identifier.
	 * @param errorLoc
	 *            the location for possible errors.
	 * @return the corresponding symbol table value.
	 */
	public SymbolTableValue get(final String cId, final ILocation errorLoc) {
		if (!containsKey(cId)) {
			final String msg = "Variable is neither declared globally nor locally! ID=" + cId;
			throw new IncorrectSyntaxException(errorLoc, msg);
		}
		return super.get(cId);
	}

	@Override
	public void beginScope() {
		super.beginScope();
		mCompoundCounter++;
		mCompoundNrStack.push(mCompoundCounter);
	}

	@Override
	public void endScope() {
		super.endScope();
		mCompoundNrStack.pop();
	}

	/**
	 * Whether the specified C variable is in the table.
	 *
	 * @param cId
	 *            the C identifier.
	 * @return true iff contained.
	 */
	public boolean containsCSymbol(final String cId) {
		return containsKey(cId);
	}

	/**
	 * Whether the specified Boogie variable is in the table.
	 *
	 * @param boogieId
	 *            the C identifier.
	 * @return true iff contained.
	 */
	public boolean containsBoogieSymbol(final String boogieId) {
		return mBoogieID2CID.containsKey(boogieId);
	}

	/**
	 * Adds an entry into the map to translate Boogie to C identifiers. <br/>
	 * Consider using <code>put()</code>
	 *
	 * @param boogieIdentifier
	 *            the Boogie identifier.
	 * @param loc
	 *            where to report errors to?
	 * @param cIdentifier
	 *            the C identifier.
	 */
	public void addToReverseMap(final String boogieIdentifier, final String cIdentifier, final ILocation loc) {
		final String old = mBoogieID2CID.put(boogieIdentifier, cIdentifier);
		if (old != null && !old.equals(cIdentifier)) {
			final String msg = "Variable with this name was already declared before:" + cIdentifier;
			throw new IncorrectSyntaxException(loc, msg);
		}
	}

	/**
	 * Get the C identifier for a Boogie identifier.
	 *
	 * @param boogieIdentifier
	 *            the Boogie identifier.
	 * @param loc
	 *            where to report errors to?
	 * @return the C identifier.
	 */
	public String getCID4BoogieID(final String boogieIdentifier, final ILocation loc) {
		if (!mBoogieID2CID.containsKey(boogieIdentifier)) {
			final String msg = "Variable not found: " + boogieIdentifier;
			throw new IncorrectSyntaxException(loc, msg);
		}
		return mBoogieID2CID.get(boogieIdentifier);
	}

	/**
	 * returns a unique number for each scope!
	 *
	 * @return a unique number for the current scope.
	 */
	public int getCompoundCounter() {
		if (mCompoundNrStack.isEmpty()) {
			return 0;
		}
		return mCompoundNrStack.peek();
	}

	/**
	 * Checks the symbol table for the given C identifier. Iff it is contained, the ASTType of this variable in the
	 * current scope is returned.
	 *
	 * @param cId
	 *            the C identifier, to look for.
	 * @param loc
	 *            the location for errors / warnings.
	 * @return the found ASTType.
	 */
	public ASTType getTypeOfVariable(final String cId, final ILocation loc) {
		return mMain.mTypeHandler.cType2AstType(loc, this.get(cId, loc).getCVariable());
	}

	public Declaration getBoogieDeclOfCDecl(final CDeclaration cDec) {
		return mCDecl2BoogieDecl.get(cDec);
	}

	/**
	 * Getter for boogieID2CID map.
	 *
	 * @return a map from boogie IDs to C IDs.
	 */
	public Map<String, String> getIdentifierMapping() {
		return Collections.unmodifiableMap(mBoogieID2CID);
	}

	public boolean existsInCurrentScope(final String name) {
		if (!containsCSymbol(name)) {
			return false;
		}
		boolean result = false;
		for (final String k : currentScopeKeys()) {
			result |= name.equals(k);
		}
		return result;
	}

	public SymbolTableValue getEntryForBoogieVar(final String boogieVarId, final ILocation loc) {
		throw new UnsupportedOperationException(); // See FlatSymbolTable.
	}
}
