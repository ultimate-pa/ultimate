/*
 * Copyright (C) 2017 Yannick Bühler (buehlery@tf.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
 * Flat hierarchy rewrite of the old symbol table for the compiler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.cdt.parser.MultiparseSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 * Multifiles: The flat symbol table is used as a replacement for the old symbol table. The old symbol table used
 * LinkedScopedHashMaps for symbol scopes and thus created a de facto copy of the AST structure. The new flat symbol
 * table was created with the goal of eliminating this duplication by leaving all the scope structuring tasks to the AST
 * and the symbol table merely connecting the scope-possessing AST nodes with their respective scopes.
 *
 * Because this does not use context information for translation (i.e. 'which scope was opened last') a different
 * approach for searching the table was needed. To accomplish this a hook is needed for all operations which access
 * scopes. This hook acts as a reference to where in the AST the translation process wants to look up symbols. Resolving
 * a scope is then possible in time logarithmic in the depth of the AST by checking the AST nodes in a direct path from
 * root to hook for scopes.
 *
 * For more details regarding scope resolution check the method's line comments.
 *
 * @author Yannick Bühler
 * @since 2017-12-09
 */
public class FlatSymbolTable {

	private static final boolean DEBUG_ENABLE_STORE_LOGGING = false;

	/**
	 * The global scope, spanning all translation units. Every translation unit points to this scope.
	 */
	private final Map<String, SymbolTableValue> mGlobalScope;
	/**
	 * Maps C nodes to scopes
	 */
	private final Map<IASTNode, Map<String, SymbolTableValue>> mCTable;
	/**
	 * The information that was collected about the multiparse project by the CDTParser
	 */
	private final MultiparseSymbolTable mMultiparseInformation;
	/**
	 * Used for assigning unique IDs to scopes
	 */
	private int mScopeCounter;
	/**
	 * Maps C nodes to scope IDs
	 */
	private final Map<IASTNode, Integer> mCScopeIDs;
	/**
	 * The non-trivial skip relation in the C-AST regarding scopes
	 */
	private final Function<IASTNode, IASTNode> mCHookSkip;
	/**
	 * Maps Boogie IDs to C IDs
	 */
	private final Map<String, String> mBoogieIdToCId;
	/**
	 * Maps C Declarations to Boogie Declarations
	 */
	private final Map<CDeclaration, Declaration> mCDeclToBoogieDecl;

	private final ILogger mLogger;

	public FlatSymbolTable(final ILogger logger, final MultiparseSymbolTable mst) {
		mLogger = logger;
		mGlobalScope = new LinkedHashMap<>();
		mCTable = new LinkedHashMap<>();
		mCScopeIDs = new HashMap<>();
		mBoogieIdToCId = new HashMap<>();
		mCDeclToBoogieDecl = new HashMap<>();
		mMultiparseInformation = mst;
		mScopeCounter = 1;
		mCHookSkip = n -> {
			if (n instanceof IASTExpression && n.getParent() instanceof IASTSwitchStatement) {
				if (((IASTSwitchStatement) n.getParent()).getControllerExpression() == n) {
					// the controller expression is not part of the scope of the switch
					// so the scope holder for the controller expression is the parent of the switch...
					return n.getParent().getParent();
				}
			}
			return n;
		};
	}

	/**
	 * Implements the generic table lookup
	 *
	 * @param hook
	 *            the hook which acts as an anchor for the current context in the AST
	 * @param id
	 *            the id of the entry to look for
	 * @param onlyInnermost
	 *            if true, only the innermost scope will be searched
	 * @return the table entry or null
	 */
	private SymbolTableValue tableFind(final IASTNode hook, final String id, final boolean onlyInnermost) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			final Map<String, SymbolTableValue> scope;
			if (cursor instanceof IASTTranslationUnit) {
				// This node references the global scope
				scope = mGlobalScope;
			} else {
				// This node may have an associated scope
				scope = mCTable.get(cursor);
			}
			if (scope != null) {
				// we have a scope: check whether the ID is found in that scope
				final SymbolTableValue resultCandidate = scope.get(id);
				if (resultCandidate != null) {
					// This scope shadows all outer (=upper) scopes
					return resultCandidate;
				}
				if (onlyInnermost) {
					// This node represents the innermost scope but doesn't contain the ID
					return null;
				}
			}
			// Check the next level of the AST for scopes
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		// we did not find the value
		return null;
	}

	/**
	 * Return the cursor on which a given symbol table value is stored. This can be used to update a symbol table value.
	 * Returns null if the value is not present.
	 */
	public IASTNode tableFindCursor(final IASTNode hook, final String id, final SymbolTableValue val) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			final Map<String, SymbolTableValue> scope;
			if (cursor instanceof IASTTranslationUnit) {
				// This node references the global scope
				scope = mGlobalScope;
			} else {
				// This node may have an associated scope
				scope = mCTable.get(cursor);
			}
			if (scope != null) {
				// we have a scope: check whether the ID is found in that scope
				final SymbolTableValue resultCandidate = scope.get(id);
				if (resultCandidate != null && val == resultCandidate) {
					// This scope shadows all outer (=upper) scopes
					return cursor;
				}
			}
			// Check the next level of the AST for scopes
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		// we did not find the value
		return null;
	}

	/**
	 * Lookup in the C-AST symbol table
	 *
	 * @see FlatSymbolTable#tableFind(IASTNode, String, Map, boolean)
	 */
	public SymbolTableValue findCSymbol(final IASTNode hook, final String id) {
		return tableFind(hook, id, false);
	}

	/**
	 * Convenience method for checking if an entry exists. Note that you should never combine it with
	 * {@link #findCSymbol(IASTNode, String)} because it will double your runtime.
	 *
	 * @see FlatSymbolTable#findCSymbol(IASTNode, String)
	 */
	public boolean containsCSymbol(final IASTNode hook, final String id) {
		return findCSymbol(hook, id) != null;
	}

	/**
	 * Finds an entry in the innermost scope
	 *
	 * @see FlatSymbolTable#findCSymbol(IASTNode, String)
	 */
	public SymbolTableValue findCSymbolInInnermostScope(final IASTNode hook, final String id) {
		return tableFind(hook, id, true);
	}

	/**
	 * Fetches the unique scope ID at the given hook
	 *
	 * @param hook
	 *            where in the AST to look for scopes
	 * @return the unique scope ID
	 */
	public int getCScopeId(final IASTNode hook) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			if (cursor instanceof IASTTranslationUnit) {
				// The global scope is 1
				return 1;
			}
			final boolean hasImplicitScope =
					cursor instanceof IASTFunctionDefinition || cursor instanceof IASTForStatement;
			final boolean hasExplicitScope =
					cursor instanceof IASTCompoundStatement && !(cursor.getParent() instanceof IASTFunctionDefinition)
							&& !(cursor.getParent() instanceof IASTForStatement);
			if (hasImplicitScope || hasExplicitScope) {
				final Integer counter = mCScopeIDs.get(cursor);
				if (counter != null) {
					return counter;
				}
				mScopeCounter++;
				mCScopeIDs.put(cursor, mScopeCounter);
				return mScopeCounter;
			}
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		return 0;
	}

	/**
	 * Stores a value in the table
	 *
	 * @param hook
	 *            anchor in the AST
	 * @param id
	 *            the ID of the value
	 * @param val
	 *            the value
	 * @see FlatSymbolTable#tableFind(IASTNode, String, boolean)
	 */
	private void tableStore(final IASTNode hook, final String id, final SymbolTableValue val) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			if (cursor instanceof IASTTranslationUnit) {
				mGlobalScope.put(id, val);
				if (DEBUG_ENABLE_STORE_LOGGING) {
					mLogger.info(String.format("%-50.50s[%-25.25s]: Storing %s to %s",
							ReflectionUtil.getCallerSignature(4), cursor.getClass().getSimpleName(), id, val));
				}
				break;
			}
			if (cursor instanceof IASTCompositeTypeSpecifier) {
				// we are inside a struct or union declaration, we do not store the fields in the symbol table.
				break;
			}

			final boolean hasImplicitScope =
					cursor instanceof IASTFunctionDefinition || cursor instanceof IASTForStatement;
			final boolean hasExplicitScope =
					cursor instanceof IASTCompoundStatement && !(cursor.getParent() instanceof IASTFunctionDefinition)
							&& !(cursor.getParent() instanceof IASTForStatement);
			if (hasImplicitScope || hasExplicitScope) {
				// This node is the scope where values are currently stored inside
				Map<String, SymbolTableValue> scopeTable = mCTable.get(cursor);
				if (scopeTable == null) {
					scopeTable = new LinkedHashMap<>();
					mCTable.put(cursor, scopeTable);
				}
				if (DEBUG_ENABLE_STORE_LOGGING) {
					mLogger.info(String.format("%-50.50s[%-25.25s]: Storing %s to %s",
							ReflectionUtil.getCallerSignature(4), cursor.getClass().getSimpleName(), id, val));
				}
				scopeTable.put(id, val);
				break;
			}
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		if (cursor == null) {
			throw new IllegalStateException("Found no possible scope holder");
		}
	}

	/**
	 * Stores a C symbol
	 *
	 * @see FlatSymbolTable#tableStore(IASTNode, String, SymbolTableValue)
	 */
	public void storeCSymbol(final IASTNode hook, final String id, final SymbolTableValue val) {
		tableStore(hook, id, val);
		mBoogieIdToCId.put(val.getBoogieName(), id);
		mCDeclToBoogieDecl.put(val.getCDecl(), val.getBoogieDecl());
	}

	/**
	 * Update an existing symbol table value with a new one.
	 */
	public void updateCSymbolFromOccurence(final IASTNode hook, final String id, final SymbolTableValue oldVal,
			final SymbolTableValue newVal) {
		final IASTNode cursor = tableFindCursor(hook, id, oldVal);
		updateCSymbolFromCursor(cursor, id, oldVal, newVal);
	}

	/**
	 * Update an existing symbol table value with a new one. The cursor must be exactly the location of the symbol.
	 */
	public void updateCSymbolFromCursor(final IASTNode cursor, final String id, final SymbolTableValue oldVal,
			final SymbolTableValue newVal) {
		if (cursor != null) {
			final Map<String, SymbolTableValue> scope;
			if (cursor instanceof IASTTranslationUnit) {
				scope = mGlobalScope;
			} else {
				scope = mCTable.get(cursor);
			}
			if (scope != null) {
				if (DEBUG_ENABLE_STORE_LOGGING) {
					mLogger.info(String.format("%-50.50s[%-25.25s]: Updating %s from %s to %s",
							ReflectionUtil.getCallerSignature(4), cursor.getClass().getSimpleName(), id, oldVal,
							newVal));
				}
				scope.put(id, newVal);
				mBoogieIdToCId.remove(oldVal.getBoogieName());
				mBoogieIdToCId.put(newVal.getBoogieName(), id);
				mCDeclToBoogieDecl.remove(oldVal.getCDecl());
				mCDeclToBoogieDecl.put(newVal.getCDecl(), newVal.getBoogieDecl());
				return;
			}
		}
		throw new IllegalArgumentException(
				"The old symbol table value could not be found in the table with the given cursor: " + cursor);
	}

	/**
	 * Fetches all values in the innermost C scope
	 *
	 * @param hook
	 *            the anchor in the C AST
	 * @return the values that are present in the innermost scope
	 */
	public Iterable<SymbolTableValue> getInnermostCScopeValues(final IASTNode hook) {
		IASTNode cursor = mCHookSkip.apply(hook);
		while (cursor != null) {
			final Map<String, SymbolTableValue> values = mCTable.get(cursor);
			if (values != null) {
				return Collections.unmodifiableCollection(values.values());
			}
			if (hasOwnScope(cursor)) {
				return Collections.emptyList();
			}
			cursor = cursor.getParent();
			cursor = mCHookSkip.apply(cursor);
		}
		return Collections.emptyList();
	}

	/**
	 * Renames an identifier given the file it is in and the original name
	 *
	 * @param filePath
	 *            The file the identifier is used in
	 * @param original
	 *            The original identifier
	 * @return the new identifier (might be the same as before)
	 */
	public String applyMultiparseRenaming(final String filePath, final String original) {
		return mMultiparseInformation.getNameMappingIfExists(filePath, original);
	}

	/**
	 * Fetches the C ID for the given Boogie ID
	 *
	 * @param boogieId
	 *            the boogie ID
	 * @return the C ID
	 */
	public String getCIdForBoogieId(final String boogieId) {
		return mBoogieIdToCId.get(boogieId);
	}

	/**
	 * Fetches the Boogie Declaration for the given C Declaration
	 *
	 * @param cDecl
	 *            the C declaration
	 * @return the Boogie Declaration
	 */
	public Declaration getBoogieDeclForCDecl(final CDeclaration cDecl) {
		return mCDeclToBoogieDecl.get(cDecl);
	}

	/**
	 * Checks whether a variable with the given boogie ID is known, used for checking if a variable is a temporary
	 * variable
	 *
	 * @param boogieId
	 *            the boogie ID
	 * @return whether the variable is contained in the symbol table
	 */
	public boolean containsBoogieSymbol(final String boogieId) {
		return mBoogieIdToCId.containsKey(boogieId);
	}

	/**
	 * Manually adds a C/Boogie ID pair to the symbol table
	 *
	 * @param boogieIdentifier
	 *            the boogie ID
	 * @param cIdentifier
	 *            the C ID
	 * @param loc
	 *            the location, for error reporting
	 */
	public void addBoogieCIdPair(final String boogieIdentifier, final String cIdentifier, final ILocation loc) {
		final String old = mBoogieIdToCId.put(boogieIdentifier, cIdentifier);
		if (old != null && !old.equals(cIdentifier)) {
			final String msg = "Variable with this name was already declared before:" + cIdentifier;
			throw new IncorrectSyntaxException(loc, msg);
		}
	}

	/**
	 * Returns the Boogie to C ID mapping
	 *
	 * @return the boogie to C ID mapping
	 */
	public Map<String, String> getBoogieCIdentifierMapping() {
		return Collections.unmodifiableMap(mBoogieIdToCId);
	}

	private static boolean hasOwnScope(final IASTNode node) {
		final boolean hasImplicitScope = node instanceof IASTFunctionDefinition || node instanceof IASTForStatement;
		final boolean hasExplicitScope =
				node instanceof IASTCompoundStatement && !(node.getParent() instanceof IASTFunctionDefinition)
						&& !(node.getParent() instanceof IASTForStatement);
		return hasImplicitScope || hasExplicitScope;
	}

	public boolean isInsideStructDeclaration(final IASTDeclarator hook) {
		IASTNode cursor = hook;
		while (cursor != null) {
			if (cursor instanceof IASTCompositeTypeSpecifier) {
				return true;
			}
			cursor = cursor.getParent();
		}
		return false;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Global: ").append(CoreUtil.getPlatformLineSeparator());
		sb.append(mGlobalScope.entrySet().stream().map(a -> a.getKey() + " " + a.getValue())
				.collect(Collectors.joining(",")));
		sb.append(CoreUtil.getPlatformLineSeparator());
		for (final Entry<IASTNode, Map<String, SymbolTableValue>> entry : mCTable.entrySet()) {
			sb.append(entry.getKey().getClass().getSimpleName()).append(" ");
			sb.append(entry.getKey().getFileLocation().getStartingLineNumber())
					.append(CoreUtil.getPlatformLineSeparator());
			sb.append(entry.getValue().entrySet().stream().map(a -> a.getKey() + " " + a.getValue())
					.collect(Collectors.joining(",")));
		}
		return sb.toString();
	}
}
