//#Safe
/*
 * Boogie code that occurs in our translation of
 * the SV-COMP benchmark `libvsync/twalock.i`.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2025-03-09
 * 
 */

procedure proc() returns ()
modifies;
{
  while (true)
  {
      while (true)
      {
          while (true)
          {
              if (false) {
              } else {
                  break;
              }
          }
          if (false) {
          } else {
              break;
          }
      }
      if (false) {
      } else {
          break;
      }
  }
}



  
