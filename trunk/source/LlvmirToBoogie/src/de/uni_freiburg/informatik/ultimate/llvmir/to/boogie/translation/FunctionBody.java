/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirToBoogie plug-in.
 * It is used to monitor the parsing of LLVM IR files and to translate them into a Boogie AST.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;

/**
 * Instances of this class are used to represent the body of a function in the Boogie AST.
 */
public class FunctionBody {
	private final ArrayList<VariableDeclaration> mFuncLocalVars;
	private final ArrayList<Statement> mFuncBlock;
	private final HashMap<String, Integer> mLabelMap;
	private int mCurrentFreeLabelCount = 0;
	private int mCurrentLabelIndex = -1;

	public FunctionBody() {
		mFuncLocalVars = new ArrayList<>();
		mFuncBlock = new ArrayList<>();
		mLabelMap = new HashMap<>();
	}

	public ArrayList<VariableDeclaration> getFuncLocalVars() {
		return mFuncLocalVars;
	}

	public ArrayList<Statement> getFuncBlock() {
		return mFuncBlock;
	}

	public HashMap<String, Integer> getLabelMap() {
		return mLabelMap;
	}

	public int getCurrentFreeLabelCount() {
		return mCurrentFreeLabelCount;
	}

	public int getCurrentLabelIndex() {
		return mCurrentLabelIndex;
	}

	public void setCurrentLabelIndex(final int currentLabelIndex) {
		if (currentLabelIndex < 0) {
			throw new IllegalArgumentException("Label index must be non-negative");
		}
		mCurrentLabelIndex = currentLabelIndex;
	}

	public void incrementCurrentLabelIndex() {
		mCurrentLabelIndex++;
	}

	public void addFuncLocalVar(final VariableDeclaration funcLocalVar) {
		mFuncLocalVars.add(funcLocalVar);
	}

	public void addFuncLocalVars(final Collection<VariableDeclaration> funcLocalVars) {
		mFuncLocalVars.addAll(funcLocalVars);
	}

	public void addFuncBlock(final Statement funcBlock) {
		mFuncBlock.add(funcBlock);
	}

	public void addFuncBlocks(final Collection<Statement> funcBlocks) {
		mFuncBlock.addAll(funcBlocks);
	}

	public void addLabel(final String label) {
		mLabelMap.put(label, mCurrentFreeLabelCount);
		mCurrentFreeLabelCount++;
	}

	/**
	 * Merges the local variables and statements of another FunctionBody into this one.
	 *
	 * @param other the FunctionBody to merge with
	 * @return this FunctionBody after merging
	 */
	public FunctionBody merge(final FunctionBody other) {
		mFuncLocalVars.addAll(other.getFuncLocalVars());
		mFuncBlock.addAll(other.getFuncBlock());
		return this;
	}
}
