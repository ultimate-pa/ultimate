/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Location in a C+ACSL program.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Jochen Hoenicke
 * @date 06.03.2012
 */
public class ReqLocation implements Serializable, ILocation {
    /**
     * Serial version UID.
     */
    private static final long serialVersionUID = -194821240021400957L;
    /**
     * The mCheckedSpecification of check/assertion applied to this node.
     */
    protected ReqCheck mCheckedSpecification;

    /**
     * Constructor.
     * 
     * @param cNode
     *            the corresponding C AST node.
     * @param type
     *            the type of check/assertion
     */
    public ReqLocation(ReqCheck checkNode) {
        mCheckedSpecification = checkNode;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
    	return mCheckedSpecification.toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getStartLine()
     */
    @Override
    public int getStartLine() {
    	return mCheckedSpecification.getStartLine();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getEndLine()
     */
    @Override
    public int getEndLine() {
    	return mCheckedSpecification.getEndLine();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getStartColumn()
     */
    @Override
    public int getStartColumn() {
        return -1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getEndColumn()
     */
    @Override
    public int getEndColumn() {
        return -1;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getFileName()
     */
    @Override
    public String getFileName() {
    	return mCheckedSpecification.getFileName();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uni_freiburg.informatik.ultimate.model.Location#getOrigin()
     */
    @Override
    public ILocation getOrigin() {
        return this;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uni_freiburg.informatik.ultimate.model.Location#checkedSpecification()
     */
    @Override
    public Check getCheck() {
    	return mCheckedSpecification;
    }

    @Override
    public boolean isLoop() {
        return false;
    }
}
