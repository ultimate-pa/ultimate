/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb.INode;
import java.util.Map;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class InnerNode
implements INode {
    public final Map<Term, Term> mWitness;
    private INode mTrueChild;
    private INode mFalseChild;

    public InnerNode(INode trueChild, INode flaseChild, Map<Term, Term> witness) {
        this.mWitness = witness;
        this.mTrueChild = trueChild;
        this.mFalseChild = flaseChild;
    }

    public INode getChild(boolean edge) {
        if (edge) {
            return this.mTrueChild;
        }
        return this.mFalseChild;
    }

    public void swapChild(INode oldChild, INode newChild) {
        if (oldChild.equals(this.mTrueChild)) {
            this.mTrueChild = newChild;
        } else if (oldChild.equals(this.mFalseChild)) {
            this.mFalseChild = newChild;
        } else {
            throw new IllegalArgumentException("the node to swap is not a child of this node");
        }
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("inner: " + this.hashCode() + this.mWitness.toString() + " -> " + this.mTrueChild.hashCode() + this.mTrueChild.toString() + " and " + this.mFalseChild.hashCode() + this.mFalseChild.toString());
        sb.append("\n");
        this.mTrueChild.toString(sb);
        this.mFalseChild.toString(sb);
    }

    @Override
    public String toString() {
        return this.mWitness.toString();
    }
}