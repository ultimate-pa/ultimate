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
 * Describes a named type given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author Markus Lindenmann
 * @date 01.11.2012
 */
public class CNamed extends CType {
    /**
     * The type this named type is mapping to.
     */
    private final CType mappedType;

    /**
     * The name that is mapped.
     */
    private final String name;
    
    /**
     * Constructor.
     * 
     * @param decl
     *            the declaration to work on.
     * @param mappedType
     *            the type this named type is referring to.
     */
    public CNamed(String name, CType mappedType) {
//        super();
        super(false, false, false, false); //FIXME: integrate those flags
        this.name = name;
        this.mappedType = mappedType;
    }
    
    /**
     * Getter for the named declaration's name.
     * 
     * @return the named declaration's name.
     */
    public String getName() {
    	return name;
    }

    /**
     * Getter for the directly mapped type.
     * 
     * @return the type this named type is referring to.
     */
    public CType getMappedType() {
        return mappedType;
    }

    /**
     * Getter for the real underlying type.
     * 
     * @return the type this named type is referring to.
     */
    @Override
	public CType getUnderlyingType() {
        CType underlying = mappedType;
        while (underlying instanceof CNamed) {
            underlying = ((CNamed) underlying).getMappedType();
        }
        return underlying;
    }

    @Override
    public String toString() {
        return getName();
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof CType)) {
            return false;
        }
        return getUnderlyingType().equals(o);
    }

	@Override
	public boolean isCompatibleWith(CType o) {
		if (!(o instanceof CType)) {
            return false;
        }
        return getUnderlyingType().isCompatibleWith(o.getUnderlyingType());
	}
	
	
	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, getUnderlyingType());
	}
}
