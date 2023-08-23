#include <iostream>
#include <vector>

namespace Geometry {

    class Point 
    {
        public:
            Point(double x, double y) : m_x(x), m_y(y) {};
            ~Point() {};

        private:
            double m_x;
            double m_y;

            friend std::ostream& operator<<(std::ostream&, const Point&);
            friend std::istream& operator>>(std::istream&, Point&);
    };
    
    std::ostream& operator<<(std::ostream& out, const Point& point)
    {
        return out << "(" << point.m_x << "," << point.m_y << ")";
    }

    std::istream& operator>>(std::istream& in, Point& point)
    {
        char c1, c2, c3;
        in >> c1 >> point.m_x >> c2 >> point.m_y >> c3;
        if (c1 != '(' || c2 != ',' || c3 != ')') {
            in.setstate(std::ios::failbit);
        }
        return in;
    }

    class Shape 
    {
    public:
        Shape(double x, double y) 
            : m_position(x, y) 
        { 
            s_count++; 
        };

        Shape(const Shape& other) 
            : m_position(other.m_position)
        {
            s_count++;
        };

        virtual ~Shape() 
        {
            s_count--;
            std::cout << "~Shape" << std::endl;
        };

        virtual Shape* Copy() const = 0;

        Point& Position()
        {
            return m_position;
        };

        const Point& Position() const
        {
            return m_position;
        };

        virtual double Area() const = 0;
        virtual const char* ClassName() const = 0;

        virtual void Print(std::ostream& out) const
        {
            out << ClassName() << Position() << " Area=" << Area();
        };

        static unsigned s_count;

    private:
        Point m_position;
    };

    unsigned Shape::s_count = 0;
    std::ostream& operator<<(std::ostream& out, const Shape& shape)
    {
        shape.Print(out);
        return out;
    };

    class Rectangle : public Shape
    {
    public: 
        Rectangle(double x, double y, double width, double height)
            : Shape(x, y), m_width(width), m_height(height)
        { };

        ~Rectangle()
        {
            std::cout << "~Rectangle" << std::endl;
        }

        Shape* Copy() const 
        {
            return new Rectangle(*this);
        };

        double Width() const { return m_width; };
        double Height() const { return m_height; };

        double Area() const { return Width() * Height(); };
        const char* ClassName() const { return "Rectangle"; };

        void Print(std::ostream& out) const 
        {
            Shape::Print(out);
            out << " a,b=" << Width() << "," << Height() << std::endl;
        }

    private:
        unsigned m_width;
        unsigned m_height;

    };

    class Square : public Rectangle
    {
    public:
        Square(double x, double y, double a)
            : Rectangle(x, y, a, a)
        {};
        ~Square()
        {
            std::cout << "~Square" << std::endl;
        };

        Shape* Copy() const 
        {
            return new Square(*this);
        };

        const char* ClassName() const { return "Square"; };

    };

    class Circle : public Shape
    {
    public:
        Circle(double x, double y, double radius) 
            : Shape(x, y), m_radius(radius) 
        {};

        ~Circle()
        {
            std::cout << "~Circle" << std::endl;
        }

        Shape* Copy() const 
        {
            return new Circle(*this);
        };

        double Radius() const { return m_radius; };
        double Area() const { return Radius() * Radius() * 3.14f; };
        const char* ClassName() const { return "Circle"; };

        void Print(std::ostream& out) const
        {
            Shape::Print(out);
            std::cout << " r=" << Radius() << std::endl;
        };

    private:
        double m_radius;
    };

    class CompositeShape : public Shape
    {
    public:
        CompositeShape(double x, double y) 
            : Shape(x, y)
        {};

        CompositeShape(const CompositeShape& other)
            : Shape(other)
        {
            Init(other);
        };

        CompositeShape& operator=(const CompositeShape& other)
        {
            if (&other != this) {
                Deinit();
                Position() = other.Position();
                Init(other);
            }
            return *this;
        }

        ~CompositeShape()
        {
            for (auto shape : m_shapes) {
                delete shape;
            }
            std::cout << "~CompositeShape" << std::endl;
        };

        Shape* Copy() const 
        {
            return new CompositeShape(*this);
        };
            
        void AddShape(Shape* shape) 
        {
            m_shapes.push_back(shape);
        };

        double Area() const 
        {
            double area = 0.0;
            for (auto shape : m_shapes) {
                area += shape->Area();
            }
            return area;
        };

        const char* ClassName() const { return "CompositeShape"; };

    private:
        void Init(const CompositeShape& cs) 
        {
            for (auto shape : cs.m_shapes) {
                AddShape(shape->Copy());
            }
        };

        void Deinit()
        {
            for (auto shape : m_shapes) {
                delete shape;
            }
            m_shapes.clear();
        };

    private:
        std::vector<Shape*> m_shapes; /*!< Member description */
    };
};

int main(void)
{
    {
        Geometry::CompositeShape cs1(0, 0);
        cs1.AddShape(new Geometry::Rectangle(1, 2, 3, 4));
        cs1.AddShape(new Geometry::Square(5, 6, 7));
        cs1.AddShape(new Geometry::Circle(8, 9, 10));

        Geometry::CompositeShape* cs2 = new Geometry::CompositeShape(1, 1);
        cs2->AddShape(new Geometry::Circle(2, 3, 4));
        cs2->AddShape(new Geometry::Square(5, 6, 7));

        cs1.AddShape(cs2);

        std::cout << cs1 << std::endl;
        std::cout << Geometry::Shape::s_count << std::endl;

        Geometry::CompositeShape cs3 = cs1;
        std::cout << cs3 << std::endl;
        std::cout << cs1 << std::endl;
        std::cout << Geometry::Shape::s_count << std::endl;


        Geometry::CompositeShape cs4 = cs1;
        std::cout << cs4 << std::endl;
        cs4 = cs3;
        std::cout << cs4 << std::endl;
        std::cout << Geometry::Shape::s_count << std::endl;

    }

    std::cout << Geometry::Shape::s_count << std::endl;

    return 0;
}
