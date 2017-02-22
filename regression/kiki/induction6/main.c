
unsigned int nondet_uint();
_Bool nondet_bool();

enum state_t {
	s0, s1, s2, s3};

enum state_t arb_state_t() {
		enum state_t some_state;
		__CPROVER_assume(some_state == s0 ||some_state == s1 || some_state == s2);
		return some_state;
	}// Returns a non-deterministic state value

enum state_t s1ors2 (){ //Returns L or M non-deterministically
	enum state_t some_state = arb_state_t(); 
	__CPROVER_assume ( (some_state == s1) || (some_state == s2) );
	//assert(0);
	return some_state;}

//Define propositions for states
_Bool p (enum state_t st) {
	return ((st==s0) || (st==s1)); }

//Define next_state relation
enum state_t trans (enum state_t st) {
	enum state_t nst = st;

	if (st == s0) nst = s0;
	else if (st == s1) nst = s1ors2 ();
	else if (st == s2) nst = s2;
	else               nst = st;
	return nst;
}

_Bool init(enum state_t s) {
	return (s == s0); }

_Bool safety(enum state_t s) {
	return (p(s)); }

void main () {

  enum state_t arb_state, next_arb_state;

__CPROVER_assume(init(arb_state)); //arb_state_t();

  while (1) {
 

	  next_arb_state = trans(arb_state);
          arb_state = next_arb_state;

          assert(safety(arb_state));

  } 
}

