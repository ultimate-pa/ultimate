/*
 * Copyright (C) 2009-2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * Master reverse trigger that is installed for a (function symbol, argument position) pair. When activated, it registers the
 * found application with the engine and adds the corresponding ReverseTriggerTrigger and back-ref.
 *
 * @author Jochen Hoenicke
 */
public final class MasterReverseTrigger extends ReverseTrigger {
	private final CClosure mEngine;
	private final FunctionSymbol mFunctionSymbol;
	private final int mArgPosition;

	static final UnifyHash<MasterReverseTrigger> sUnifier = new UnifyHash<>();

	public static MasterReverseTrigger of(final CClosure engine, final FunctionSymbol functionSymbol,
			final int argPosition) {
		final int hash = HashUtils.hashJenkins(argPosition, functionSymbol);
		for (final MasterReverseTrigger masterReverseTrigger : sUnifier.iterateHashCode(hash)) {
			if (masterReverseTrigger.mFunctionSymbol == functionSymbol
					&& masterReverseTrigger.mArgPosition == argPosition) {
				return masterReverseTrigger;
			}
		}
		final MasterReverseTrigger masterReverseTrigger = new MasterReverseTrigger(engine, functionSymbol, argPosition);
		sUnifier.put(hash, masterReverseTrigger);
		engine.insertFindTrigger(functionSymbol, masterReverseTrigger);
		return masterReverseTrigger;
	}

	private MasterReverseTrigger(final CClosure engine, final FunctionSymbol functionSymbol, final int argPosition) {
		super();
		mEngine = engine;
		mFunctionSymbol = functionSymbol;
		mArgPosition = argPosition;
	}

	@Override
	public FunctionSymbol getFunctionSymbol() {
		return mFunctionSymbol;
	}

	@Override
	public CCTerm getArgument() {
		return null;
	}

	@Override
	public int getArgPosition() {
		/* this is a find trigger, so it must return -1. */
		return -1;
	}

	@Override
	public void activate(final CCAppTerm appTerm, final boolean isFresh) {
		assert appTerm.getFunctionSymbol() == mFunctionSymbol;
		final ReverseTriggerTrigger reverseTriggerTrigger = new ReverseTriggerTrigger(this, appTerm, mArgPosition);
		mEngine.addSignature(reverseTriggerTrigger);
	}
}
