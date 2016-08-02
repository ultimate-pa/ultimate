/*
 * PDebounceValidation.c
 *
 *    @DATE: 25.10.2012
 * @AUTHORS: ansch05
 */

/*****************************************************************************
 * @CWE-ID: 440
 * @REQUIRES: 
 * @LIBRARIES: //Library
 * @CONSEQUENCES:
 * @OS:
 * @SCHEDULING:
 * @INIT:
 * @SHUTDOWN:
 * @ISRS:
 * @THREADS:
 *****************************************************************************/
/*****************************************************************************
 * @DESCRIPTION: This test case implements a design error.
 * Two (redundant) inputs are separately debounced (on/off delay). 
 * The inputs are identical in most cases. The inputs change rarely.
 * The asumption is, that the debounced comparison of
 * the debounced inputs will not show inequality. The problem is that if the
 * two inputs differ in one step, the debouncing can lead to different debounced
 * states of the inputs if the inputs continously change exactly after debounce
 * time.
 *****************************************************************************/

/*****************************************************************************
 *** System Includes                                                       ***
 *****************************************************************************/

/*****************************************************************************
 *** Own Includes                                                          ***
 *****************************************************************************/

#include "tclranges.h"
#include "tclassert.h"
#include "PDebounceValidation.h"
/*****************************************************************************
 *** Defines                                                               ***
 *****************************************************************************/


/*****************************************************************************
 *** Prototypes                                                            ***
 *****************************************************************************/
uint8 debounce_u8(uint8 _signal_u8, uint8 _debounceThresh_u8,
			   uint8 _lastOutput_u8, uint8 * _delay_u8);



/*****************************************************************************
 *** Implementation                                                        ***
 *****************************************************************************/
 
#define  PDebounceValidationInputThreshold 10
#define  PDebounceValidationCompareThreshold 10
 
void PDebounceValidation(void)
{
	static uint8 signal_u8 = 0;
	static uint8 plausiSignal_u8 = 0;
	static uint8 signalDeb_u8 = 0;
	static uint8 plausiSignalDeb_u8 = 0;
	static uint8 signalDelay_u8 = 0;
	static uint8 plausiSignalDelay_u8 = 0;
	static uint8 comparisonDelay_u8 = 0;
	static uint8 comparisonDeb_u8 = (1==1);

	uint8 comparison_u8 = 0;

	while (tclRange_b(0,1))
	{
		if (tclRange_u8(0,255)== 0) {
			signal_u8 = tclRange_u8(0,255);
			if (tclRange_u8(0,255)== 0) {
				plausiSignal_u8 = tclRange_u8(0,255);
			}
			else {
				plausiSignal_u8 = signal_u8;
			}
		}
		signalDeb_u8 = debounce_u8(signal_u8, PDebounceValidationInputThreshold, signalDeb_u8, &signalDelay_u8);
		plausiSignalDeb_u8 = debounce_u8(plausiSignal_u8, PDebounceValidationInputThreshold, plausiSignalDeb_u8, &plausiSignalDelay_u8);

		comparison_u8 = (signalDeb_u8 == plausiSignalDeb_u8);
		comparisonDeb_u8 = debounce_u8(comparison_u8, PDebounceValidationCompareThreshold, comparisonDeb_u8, &comparisonDelay_u8);
		TclAssert(comparisonDeb_u8 > 0); /* <- Bug position */
	}
}

uint8 debounce_u8(uint8 _signal_u8, uint8 _debounceThresh_u8,
			   uint8 _lastOutput_u8, uint8 * _delay_u8)
{
	uint8 output_u8 = _lastOutput_u8;
	if (_delay_u8 != NULL)
	{
		if (_signal_u8 != _lastOutput_u8)
		{
			(*_delay_u8)++;
			if (*_delay_u8 >= _debounceThresh_u8)
			{
				*_delay_u8 = 0;
				output_u8 = _signal_u8;
			}
		} else {
			*_delay_u8 = 0;
		}
		return output_u8;
	} else {
		return _signal_u8;
	}

}
