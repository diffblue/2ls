#define TRUE 1
#define FALSE 0

struct state_elements_Traffic_Light {
  unsigned char Light_Sign;
};
struct state_elements_Traffic_Light  sTraffic_Light;

 // parameters
#define RED_LIGHT  0
#define GREEN_LIGHT  1
#define YELLOW_LIGHT  2
  
int main() {
  sTraffic_Light.Light_Sign = RED_LIGHT;
  
  while(1) {
    sTraffic_Light.Light_Sign = GREEN_LIGHT;
    assert((sTraffic_Light.Light_Sign != 1));
  }
  return 1;
}
