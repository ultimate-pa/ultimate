/*
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for 
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 * 
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

/**
 * Class that captures all strings used as xml tags or xml constants.
 * 
 * @author Roland Meyer
 * 
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.schemas
 */
public class XMLTags {

    public static final String SYNC_PREFIX = "S";

    public static final String OR_CONST = "OR";
    public static final String AND_CONST = "AND";
    public static final String NOT_CONST = "NOT";
    public static final String CHOP_CONST = "CHOP";

    public static final String GREATER_CONST = "greater";
    public static final String GREATEREQUAL_CONST = "greaterequal";
    public static final String EQUAL_CONST = "equal";
    public static final String NOTEQUAL_CONST = "notequal";
    public static final String LESSEQUAL_CONST = "lessequal";
    public static final String LESS_CONST = "less";

    public static final String TRUE_CONST = "true";
    public static final String FALSE_CONST = "false";

    public static final String PARSER_VALIDATION_FEATURE = "http://xml.org/sax/features/validation";
    public static final String PARSER_SCHEMA_VALIDATION_FEATURE = "http://apache.org/xml/features/validation/schema";
    public static final String PARSER_SCHEMA_LOADEXTDTD_FEATURE = "http://apache.org/xml/features/nonvalidating/load-external-dtd";

    public static final String TRACE_TAG = "trace";
    public static final String PHASE_TAG = "phase";
    public static final String EVENT_TAG = "event";

    public static final String STATEINVARIANT_TAG = "stateInvariant";
    public static final String FORBIDDENEVENT_TAG = "forbiddenEvent";

    public static final String MCFORMS_TAG = "mcForms";
    public static final String MCFORmTAG = "mcForm";
    public static final String MCTRACE_TAG = "mcTrace";

    public static final String ENTRYSYNC_TAG = "entrySync";
    public static final String EXITSYNC_TAG = "exitSync";

    public static final String TESTFORmTAG = "testForm";
    public static final String TFTREE_TAG = "tfTree";

    public static final String OPERATOR_TAG = "operator";

    public static final String NAME_Tag = "name";
    public static final String SPEC_TAG = "spec";

    public static final String TIMEBOUND_TAG = "timeBound";
    public static final String BOUND_TAG = "bound";

    public static final String XMLNS_TAG = "xmlns:xsi";
    public static final String SCHEMAINST_TAG = "http://www.w3.org/2001/XMLSchema-instance";
    public static final String NONAMESPACELOC_TAG = "xsi:noNamespaceSchemaLocation";

    public static final String MODELCHECKFORMSCHEMA_PATH = "../schemas/ModelCheckForm.xsd";
    public static final String PEASCHEMA_PATH = "../schemas/PEA.xsd";

    public static final String PEANET_TAG = "peaNet";
    public static final String PEA_TAG = "pea";
    public static final String PHASES_TAG = "phases";
    public static final String TRANSITIONS_TAG = "transitions";
    public static final String INITIAL_TAG = "initial";
    public static final String VARIABLES_TAG = "variables";
    public static final String VARIABLE_TAG = "variable";
    public static final String CLOCKS_TAG = "clocks";
    public static final String CLOCK_TAG = "clock";
    public static final String EVENTS_TAG = "events";

    public static final String TRANSITION_TAG = "transition";
    public static final String SOURCE_TAG = "source";
    public static final String TARGET_TAG = "target";
    public static final String GUARD_TAG = "guard";
    public static final String RESET_TAG = "reset";
    public static final String INVARIANT_TAG = "invariant";
    public static final String CLOCKINVARIANT_TAG = "clockInvariant";

    public static final String TYPE_TAG = "type";
    public static final String DEFAULTTYPE_CONST = "default_type";

    public static final String BOOLEANEXPRESSION_TAG = "booleanExpression";
    public static final String RANGEEXPRESSION_TAG = "rangeExpression";
    public static final String EVENTEXPRESSION_TAG = "eventExpression";

    public static final String EXPRESSION_TAG = "expression";
    public static final String FORMULATREE_TAG = "formulaTree";

    public static final String ALLOWEMPTY_TAG = "allowEmpty";

    public static final String Z_TAG = "zTag";
}
