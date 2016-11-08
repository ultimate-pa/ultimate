/*
 * DD 2016-10-11
 * Anonymous struct leads to exception: 
 *
 * IllegalArgumentException: RValues cannot have array type
 */
 
union __anonunion_eu_159 {
   char stream[0];
};

struct __anonstruct_gdth_evt_data_158 {
   union __anonunion_eu_159 eu;
};

typedef struct __anonstruct_gdth_evt_data_158 gdth_evt_data;
struct __anonstruct_gdth_evt_str_164 {
   int event_source ;
   gdth_evt_data event_data ;
};

typedef struct __anonstruct_gdth_evt_str_164 gdth_evt_str;

static gdth_evt_str ebuffer[100U]  ;

int main() 
{ 
    ebuffer[0].event_source;      
}