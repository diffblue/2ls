#include <limits.h>

struct SDL_Rect
{
  signed short int x;
  signed short int y;
  unsigned short int h;
  unsigned short int w;
};

struct SDL_Surface
{
  unsigned int h;
  unsigned int w;
};

struct SDL_Surface img;

// c::createBack
// file Util.h line 35
//void createBack(struct SDL_Surface **back_surface)
void createBack(struct SDL_Surface *back_surface)
{
  __CPROVER_assume(1<=img.h && img.h<=16384);
  __CPROVER_assume(1<=img.w && img.w<=16384);
  __CPROVER_assume(back_surface->w<=16384);
  __CPROVER_assume(back_surface->h<=16384);
  signed int x;
  signed int y;
  struct SDL_Rect pos;
//  struct SDL_Surface *img = images[(signed long int)img_back]->image;
/*  *back_surface=SDL_CreateRGBSurface((unsigned int)1, screen->w + img->w, screen->h + img->h, (signed int)screen->format->BitsPerPixel, (unsigned int)0, (unsigned int)0, (unsigned int)0, (unsigned int)0);
  if(*back_surface == ((struct SDL_Surface *)NULL))
  {
    char *return_value_SDL_GetError$1;
    return_value_SDL_GetError$1=SDL_GetError();
    fprintf$link10(stderr, "Error creating surm_face: %s\n", return_value_SDL_GetError$1);
    fflush(stderr);
    return;
    } */

  y = 0;
//  for( ; !(y >= (*back_surface)->h); y = y + img->h)
  for( ; !(y >= back_surface->h); y = y + img.h)
  {
    x = 0;
//    for( ; !(x >= (*back_surface)->w); x = x + img->w)
    for( ; !(x >= back_surface->w); x = x + img.w)
    {
      pos.x = (signed short int)x;
      pos.y = (signed short int)y;
      pos.w = (unsigned short int)img.w;
      pos.h = (unsigned short int)img.h;
//      pos.w = (unsigned short int)img->w;
//      pos.h = (unsigned short int)img->h;
//      SDL_UpperBlit(img, (struct SDL_Rect *)NULL, *back_surface, &pos);
    }
  }
}

void main()
{
  struct SDL_Surface back_surface;
  createBack(&back_surface);
}
