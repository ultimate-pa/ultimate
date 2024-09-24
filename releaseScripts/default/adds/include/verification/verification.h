/*
 * Copyright (C) 2024 Manuel Bentele
 * 
 * This file is part of the ULTIMATE program analysis framework.
 * 
 * The ULTIMATE program analysis framework is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 * 
 * The ULTIMATE program analysis framework is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE program analysis
 * framework. If not, see http://www.gnu.org/licenses/.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE program analysis framework, or
 * any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing
 * parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE program analysis framework
 * grant you additional permission to convey the resulting work.
 */

/**
 * Verification functions and data types for static or dynamic program analysis.
 * 
 * The corresponding implementation of the verification functions and data types can be selected by defining one of the
 * following macros:
 * 
 *  - STATIC_VERIFICATION_ULTIMATE to select functions and data types built into Ultimate for static analysis.
 *  - DYNAMIC_VERIFICATION to select functions and data types for dynamic program analysis (runtime verification).
 * 
 * \author Manuel Bentele
 * \version 0.2.4
 */

#ifndef __VERIFICATION_H
#define __VERIFICATION_H

#ifdef __cplusplus
extern "C" {
#endif

#if defined(STATIC_VERIFICATION_ULTIMATE) && !defined(DYNAMIC_VERIFICATION)
#include <verification/ultimate.h>
#elif defined(DYNAMIC_VERIFICATION) && !defined(STATIC_VERIFICATION_ULTIMATE)
#include <verification/compile.h>
#else
#error "Unsupported verification method: Must be either STATIC_VERIFICATION_ULTIMATE or DYNAMIC_VERIFICATION!"
#endif

#ifdef __cplusplus
}
#endif

#endif /* __VERIFICATION_H */
