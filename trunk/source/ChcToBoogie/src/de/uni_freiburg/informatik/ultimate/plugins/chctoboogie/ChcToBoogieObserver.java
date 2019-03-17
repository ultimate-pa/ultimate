/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ChcToBoogie plug-in.
 *
 * The ChcToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ChcToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ChcToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ChcToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ChcToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcPreMetaInfoProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugin.chctoboogie.preferences.ChcToBoogiePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Does the main work of this plugin. Takes a set of HornClause objects from the previous plugin and converts it into a
 * Boogie Unit that is safe if and only if the input set of Horn clauses is satisfiable.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class ChcToBoogieObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private Unit mBoogieUnit;

	private Term2Expression mTerm2Expression;
	private final String mNameOfMainEntryPointProc;
	private ManagedScript mManagedScript;
	private TypeSortTranslator mTypeSortTanslator;
	private HcSymbolTable mHcSymbolTable;
	private final ILocation mLocation;

	private boolean mEncodeAsGotoProgram;

	private final IPreferenceProvider mPrefs;
	private String mGotoProcName;
	private String mGotoVarName;

	public ChcToBoogieObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mNameOfMainEntryPointProc = "Ultimate.START";
		mLocation = new BoogieLocation(this.getClass().getName(), 0, 0, 0, 0);
		mPrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialization needed
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mBoogieUnit;
	}

	@Override
	public boolean process(final IElement root) throws Exception {

		if (!(root instanceof HornClauseAST)) {
			return true;
		}

		final HornAnnot annot = HornAnnot.getAnnotation(root);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Printing the following HornClause set:");
			mLogger.debug(annot);
		}

		if (!annot.hasCheckSat()) {
			generateDummyBoogieAst();
			return true;
		}

		final List<HornClause> hornClausesRaw = annot.getHornClauses();
		mManagedScript = annot.getScript();
		mHcSymbolTable = annot.getSymbolTable();

		{
			final HashRelation<Sort, IBoogieType> sortToType = new HashRelation<>();
			sortToType.addPair(mManagedScript.getScript().sort("Int"), BoogieType.TYPE_INT);
			sortToType.addPair(mManagedScript.getScript().sort("Real"), BoogieType.TYPE_REAL);
			sortToType.addPair(mManagedScript.getScript().sort("Bool"), BoogieType.TYPE_BOOL);
			mTypeSortTanslator = new TypeSortTranslator(sortToType, mManagedScript.getScript(), mServices);
		}

		mTerm2Expression = new Term2Expression(mTypeSortTanslator, mHcSymbolTable, mManagedScript);

		// final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses =
		// sortHornClausesByHeads(hornClausesRaw);
		final ChcPreMetaInfoProvider preAnalysis = new ChcPreMetaInfoProvider(hornClausesRaw, mHcSymbolTable);

		mGotoVarName = "gotoSwitch";
		final GenerateBoogieAstHelper helper = new GenerateBoogieAstHelper(mLocation, mHcSymbolTable, mTerm2Expression,
				mTypeSortTanslator, mNameOfMainEntryPointProc);
		if (mPrefs.getBoolean(ChcToBoogiePreferenceInitializer.ENCODE_AS_GOTO_PROGRAM)) {
			mHcSymbolTable.setGotoProcMode(true);
			mBoogieUnit = new GenerateGotoBoogieAst(preAnalysis, helper, mGotoVarName).getResult();
		} else {
			mHcSymbolTable.setGotoProcMode(false);
			mBoogieUnit = new GenerateBoogieAst(preAnalysis.getHornClausesSorted(), helper).getResult();
		}

		return true;
	}

	/**
	 * Generate a Boogie AST that has no specifications. (used in case there is no check-sat in the original file so we
	 * do not get a PositiveResult).
	 */
	private void generateDummyBoogieAst() {
		final Body body = new Body(mLocation, new VariableDeclaration[0], new Statement[0]);

		final Procedure proc = new Procedure(mLocation, new Attribute[0], mNameOfMainEntryPointProc, new String[0],
				new VarList[0], new VarList[0], new Specification[0], body);

		mBoogieUnit = new Unit(mLocation, new Declaration[] { proc });
	}

}
