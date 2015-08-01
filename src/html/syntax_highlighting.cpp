/*******************************************************************\

Module: Syntax Highlighting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

// may wish to try http://www.gnu.org/software/src-highlite/

#include <map>
#include <ostream>
#include <cstring>
#include <cassert>

#include "../html/html_escape.h"
#include "syntax_highlighting.h"

/*******************************************************************\

Function: is_keyword

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *keywords[]=
{ 
  "auto", "_Bool", "break", "case", "char", "_Complex", "const", "continue",
  "default", "do", "double", "else", "enum", "extern", "float", "for",
  "goto", "if", "inline", "int", "long", "register", "restrict", "return",
  "short", "signed", "sizeof", "static", "struct", "switch", "typedef",
  "union", "unsigned", "void", "volatile", "while", "__float128",
  "__int128", "__int8", "__int16", "__int32", "__int64", "__ptr32",
  "__ptr64", "__complex__", "__complex", "__real__" , "__real", "__imag__" ,
  "__imag", "offsetof", "__asm", "asm", "__asm__", "bool", "catch", "class",
  "constexpr", "delete", "decltype", "explicit", "friend", "mutable",
  "namespace", "new", "nullptr", "operator", "private", "protected",
  "public", "static_assert", "template", "this", "thread_local", "throw",
  "typeid", "typename", "using", "virtual", "wchar_t", "typeof", NULL
};

bool is_keyword(const std::string &token)
{
  for(unsigned i=0; keywords[i]!=NULL; i++)
  {
    if(strcmp(keywords[i], token.c_str())==0)
      return true;
  }
  
  return false;
}
  
/*******************************************************************\

   Class: tokenizert

 Purpose:

\*******************************************************************/

const char *tokens[]=
{ "++", "+=", "--", "-=", "&&", "&=", "||", "|=", "/*",
  "*/", "//", "%=", "/=", "<<", ">>", "<<=", ">>=", "==",
  "!=", "<=", ">=", "::", "->", "##", ".*", "->*", NULL };
  
class tokenizert
{
public:
  explicit tokenizert(const std::string &_buf):buf(_buf)
  {
  }
  
  std::string get();
  std::string peek();
  std::string buf;
  bool eol() const { return buf.empty(); }

  char get_char()
  {
    if(buf.empty()) return 0;
    char result=buf[0];
    buf.erase(0, 1);
    return result;
  }
  
  static inline bool is_identifier_char(char ch)
  {
    return isalnum(ch) || ch=='_';
  }
};

/*******************************************************************\

Function: tokenizert::peek

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string tokenizert::peek()
{
  if(buf.empty()) return buf;

  char first=buf[0];
  
  unsigned pos=1;
  
  if(is_identifier_char(first))
  {
    // identifier or keyword or number
    for(pos=1; pos<buf.size() && is_identifier_char(buf[pos]); pos++);
  }
  else if(first=='"' || first=='\'')
  {
    // string literal or character literal
    while(pos<buf.size())
    {
      if(buf[pos]==first)
        break; // end
      else if(buf[pos]=='\\' && (pos+1)<buf.size()) // escape
        pos+=2;
      else
        pos++;
    }
  }
  else
  {
    for(pos=1; pos<buf.size(); pos++)
    {
      bool match=false;
    
      for(unsigned t=0; tokens[t]!=NULL; t++)
      {
        if(strncmp(tokens[t], buf.c_str(), pos)==0)
        {
          match=true;
          break;
        }
      }

      // no more matches
      if(!match)
      {
        if(pos!=1) pos--;
        break;
      }
    }
  }
  
  return buf.substr(0, pos);
}

/*******************************************************************\

Function: tokenizert::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string tokenizert::get()
{
  std::string result=peek();
  buf.erase(0, result.size());
  return result;
}

/*******************************************************************\

Function: syntax_highlightingt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void syntax_highlightingt::operator()(const std::string &line)
{
  tokenizert tokenizer(line);
  
  while(true)
  {
    std::string token=tokenizer.peek();
    if(token==" ") out << tokenizer.get(); else break;
  }

  // open tags  
  if(!strong_class.empty())
    out << "<strong class=\"" << strong_class << "\">";
    
  if(comment) out << "<cite>";

  std::string token;  
  
  std::map<std::string, unsigned> var_count;

  while(!tokenizer.eol())
  {
    if(comment)
    {
      std::string buf;
      bool end_of_comment=false;
      
      while(!end_of_comment)
      {
        char ch=tokenizer.get_char();
        if(ch==0) break;
        buf+=ch;
        if(buf.size()>=2 && buf[buf.size()-2]=='*' && buf[buf.size()-1]=='/')
          end_of_comment=true;
      }
      
      out << html_escape(buf);

      if(end_of_comment)
      {
        out << "</cite>";
        comment=false;
      }
    }
    else
    {
      token=tokenizer.get();
      assert(!token.empty());

      if(isdigit(token[0])) // numeral
      {
        out << html_escape(token);
      }
      else if(isalpha(token[0]))
      {
        if(is_keyword(token))
          out << "<em>" << html_escape(token) << "</em>";
        else
        {
          if(identifier_tooltip)
            out << "<var onMouseOver=\"var_tooltip('"
                << token << id_suffix << "', '" << line_no 
                << "." << ++var_count[token] << "');\""
                   " onMouseOut=\"tooltip.hide();\""
                   ">";
          else
            out << "<var>";
          
          out << html_escape(token);

          out << "</var>";
        }
      }
      else if(token=="/*")
      {
        comment=true;
        out << "<cite>" << token;
      }
      else if(token=="//")
      {
        out << "<cite>" << token;
        while(!(token=tokenizer.get()).empty())
          out << html_escape(token);
        out << "</cite>";
      }
      else if(token[0]=='"' || token[0]=='\'')
      {
        out << "<kbd>" << html_escape(token) << "</kbd>";
      }
      else
      {
        // hack to distinguish lhs from rhs without parsing
        #if 0
        if(token=="+=" || token=="=" ||
           token=="-=" || token=="<<=" ||
           token==">>=" || token=="&=" ||
           token=="^=" || token=="|=")
          lhs=false;
        else if(token==";")
          lhs=true;
        #endif

        out << html_escape(token);
      }
    }
  }

  // close tags  
  if(comment) out << "</cite>";
  if(!strong_class.empty()) out << "</strong>";
  
  out << "\n";
}

